open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Linq

module Expr =  

    type BinOp = 
        | Eq 
        | Gt 
        | Lt 
        | Gte 
        | Lte
        | And 
        | Or  

    type UnOp = 
        | Not 
        | Neg 

    type QueryExpr = 
        | Binary of BinOp * QueryExpr * QueryExpr
        | Unary of UnOp * QueryExpr
        | MemberAccess of MemberInfo

    type Query = 
        { Where : QueryExpr option
          Projections : QueryExpr list }
        static member Empty = 
            { Where = None; Projections = [] }


module Patterns = 

    let (|MethodCall|_|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Call, (:? MethodCallExpression as e) -> 
            Some ((match e.Object with null -> None | obj -> Some obj), e.Method, Seq.toList e.Arguments)
        | _ -> None

    let (|MethodWithName|_|)   (s:string) (m:MethodInfo)   = if s = m.Name then Some () else None
    let (|PropertyWithName|_|) (s:string) (m:PropertyInfo) = if s = m.Name then Some () else None

    let (|Quote|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Quote, (:? UnaryExpression as ce) ->  ce.Operand
        | _ -> e

    let (|Lambda|_|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Lambda, (:? LambdaExpression as ce) ->  Some (Seq.toList ce.Parameters, ce.Body)
        | _ -> None

    let (|LambdaProjection|_|) (e:Expression) =
        match e with
        | Lambda (sourceType::_, body) ->
            match body.NodeType, body with
            | ExpressionType.MemberAccess, (:? MemberExpression as me) -> 
                Some (body.Type, [me.Member])
            | ExpressionType.New, (:? NewExpression as ne) ->
                let projectionMap = 
                    ne.Arguments 
                    |> Seq.fold (fun s a -> 
                         match a.NodeType, a with
                         | ExpressionType.MemberAccess, (:? MemberExpression as me) -> 
                            me.Member :: s
                         | _, _  -> s
                    ) ([])
                Some (body.Type, projectionMap |> List.rev)
            | _, _ -> None
        | _ -> None


module Expression = 

    open Expr
    open Patterns
    open System.Collections.Generic
    open Microsoft.FSharp.Linq.RuntimeHelpers

    let tupleTypes = 
        [|  typedefof<System.Tuple<_>>,               typedefof<AnonymousObject<_>>
            typedefof<_ * _>,                         typedefof<AnonymousObject<_, _>>
            typedefof<_ * _ * _>,                     typedefof<AnonymousObject<_, _, _>>
            typedefof<_ * _ * _ * _>,                 typedefof<AnonymousObject<_, _, _, _>>
            typedefof<_ * _ * _ * _ * _>,             typedefof<AnonymousObject<_, _, _, _, _>>
            typedefof<_ * _ * _ * _ * _ * _>,         typedefof<AnonymousObject<_, _, _, _, _, _>>
            typedefof<_ * _ * _ * _ * _ * _ * _>,     typedefof<AnonymousObject<_, _, _, _, _, _, _>>
            typedefof<_ * _ * _ * _ * _ * _ * _ * _>, typedefof<AnonymousObject<_, _, _, _, _, _, _, _>> |]

    let tupleToAnonymousTypeMap = 
        let dict = new Dictionary<Type,Type>()
        for (tupleTy,anonTy) in tupleTypes do dict.[tupleTy] <- anonTy
        dict        

    let tupleToAnonType  (ty:Type) = 
        let t = ty.GetGenericTypeDefinition()
        tupleToAnonymousTypeMap.[ty]
    let map state (e:Expression) = 
        let walk state (e:Expression) = 
            printfn "Walking %A" e
            match e with 
            | MethodCall(None, (MethodWithName "Select"), [source; (Quote (LambdaProjection (retType, projs)))]) ->
                let source = (source :?> ConstantExpression)
                let r = { state with Projections = projs |> List.map MemberAccess }
                printfn "Ret: %A" r
                r
            | _ -> state

        walk state e

type QueryProvider(state, executor : Expr.Query -> seq<obj>) =
    let rec reduceType (expr:Expr.QueryExpr) = 
        match expr with 
        | Expr.MemberAccess ma ->
            match ma.MemberType with 
            | MemberTypes.Property -> (ma :?> PropertyInfo).PropertyType
            | MemberTypes.Method -> (ma :?> MethodInfo).ReturnType
            | MemberTypes.Field -> (ma :?> FieldInfo).FieldType
            | a -> failwithf "Unable to reduce type %A" a
        | Expr.Unary (_,a) -> reduceType a
        | Expr.Binary (_, a, b) -> 
            let a, b = reduceType a, reduceType b 
            if a = b 
            then a 
            else failwithf "Unmatching types %A %A" a b 

    let toIQueryable (query:Expr.Query) = 
        let returnType = 
            match query.Projections with 
            | [] -> typeof<unit>
            | [a] -> reduceType a
            | a -> 
                 List.map reduceType a 
                 |> List.toArray 
                 |> FSharpType.MakeTupleType
                 |> Expression.tupleToAnonType

        let ty = typedefof<Queryable<_>>.MakeGenericType(returnType)
        ty.GetConstructors().[0].Invoke([|query; executor|]) :?> IQueryable
    
    interface IQueryProvider with
        member x.CreateQuery(e:Expression) : IQueryable =
            Expression.map state e 
            |> toIQueryable

        member x.CreateQuery<'T>(e:Expression) : IQueryable<'T> = 
            Expression.map state e 
            |> toIQueryable  
            :?> IQueryable<'T>
        member x.Execute(e:Expression) : obj =
            Expression.map state e |> executor |> box

        member x.Execute<'a>(e:Expression) : 'a =
            Expression.map state e 
            |> executor
            |> unbox<'a>

and Queryable<'T>(state, executor) =
     
     interface IQueryable<'T> with 
        member x.GetEnumerator() = 
           let iq = (x :> IQueryable)
           iq.Provider.Execute<seq<obj>>(iq.Expression).Cast<'T>().GetEnumerator()

     interface IQueryable with
        member x.Provider = new QueryProvider(state, executor) :> IQueryProvider
        member x.Expression =  Expression.Constant(x,typeof<IQueryable<'T>>) :> Expression 
        member x.ElementType = typeof<'T>
        member x.GetEnumerator() = 
            let iq = (x :> IQueryable)
            (iq.Provider.Execute<Collections.IEnumerable>(iq.Expression)).GetEnumerator() 


type Course = {
    CourseId : int
    CourseName : string
}

type Student = {
    StudentId : int
    Name : string
    Age : int
}

type CourseSelection = {
    Id : int
    StudentId : int
    CourseId : int
}

let students = [
    { StudentId = 1; Name = "Tom"; Age = 21 }
    { StudentId = 2; Name = "Dave"; Age = 21 }
    { StudentId = 3; Name = "Anna"; Age = 22 }
    { StudentId = 4; Name = "Sophie"; Age = 21 }
    { StudentId = 5; Name = "Richard"; Age = 20 }
]

let applyProjection (ma:MemberInfo) (a:obj) = 
    match ma.MemberType with 
    | MemberTypes.Property -> (ma :?> PropertyInfo).GetValue(a)
    | MemberTypes.Method -> (ma :?> MethodInfo).Invoke(a, [||]) 
    | MemberTypes.Field -> (ma :?> FieldInfo).GetValue(a)
    | a -> failwithf "Unable to reduce type %A" a

let q = new Queryable<Student>(Expr.Query.Empty, fun q -> 
    let t = 
        q.Projections 
        |> List.map (function 
                     | Expr.MemberAccess ma -> 
                        fun x -> System.Convert.ChangeType(applyProjection ma x, typeof<int>) 
                     | a -> failwithf "Unknown %A" a)
    seq{
        for s in students do 
            for p in t do 
                yield (p s)
    } 
)

let sudentProjection = 
    query { 
        for student in q do
        select student.Age
    } |> Seq.toArray