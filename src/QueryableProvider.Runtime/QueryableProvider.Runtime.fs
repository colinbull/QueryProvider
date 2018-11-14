namespace MyNamespace

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open Microsoft.FSharp.Reflection
open System.Runtime.CompilerServices

[<AutoOpen>]
module Extensions = 

    type MemberInfo with 

    [<Extension>]
    member ma.GetValue(a:obj) = 
        match ma.MemberType with 
        | MemberTypes.Property -> 
            let prop = (ma :?> PropertyInfo)
            prop.GetValue(a)
        | MemberTypes.Method -> 
            let methd = (ma :?> MethodInfo)
            methd.Invoke(a, [||])
        | MemberTypes.Field -> 
            let fld = (ma :?> FieldInfo)
            fld.GetValue(a)
        | _ -> failwithf "Unable to get member info value for type %A" ma.MemberType
    

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
        | Const of Type * obj
        | MemberAccess of MemberInfo

    type Query = 
        { Filter : (Type * QueryExpr) option
          Projections : QueryExpr list }
        static member Empty = 
            { Filter = None; Projections = [] }

    let getValue (q:QueryExpr) = 
        match q with 
        | Const (t, o) -> (fun _ -> o)
        | MemberAccess ma -> ma.GetValue
        | a -> failwithf "Unable to get value from %A" a

    let preComputeFilterExpression (q:Query) = 
        match q.Filter with 
        | None -> (fun _ -> true)
        | Some (_,x) -> 
            let rec walkExpr (q:QueryExpr) = 
                match q with
                |  Binary(op, x ,y) -> 
                    match op with 
                    | Eq -> (fun s -> (getValue x s) = (getValue y s))
                    | Gt -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) > 0))
                    | Lt -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) < 0))
                    | Gte -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) >= 0))
                    | Lte -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) <= 0))
                    | And -> (fun s -> (walkExpr x s) && (walkExpr y s))
                    | Or -> (fun s -> (walkExpr x s) || (walkExpr y s))
                | _ -> failwithf "%A not supported for filter expressions" q
            walkExpr x

    let preComputeProjectionExpression (ty:Type) (q:Query) = 
        let projected = 
            q.Projections |> List.map getValue

        fun x -> Activator.CreateInstance(ty, [| for projection in projected -> (projection x)|]) 

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

    let (|PropertyGet|_|) (e:Expression) = 
         match e with 
         | :? MemberExpression as me -> 
            Some(Expr.MemberAccess me.Member)
         | _ -> None 

    let (|Constant|_|) (e:Expression) =
        match e with
        | :? ConstantExpression as ce -> Some(Expr.Const(ce.Type, ce.Value))
        | _ -> None
    
    let (|BinaryExpression|_|) (e:Expression) =
        let mapBinaryOperator = function
            | ExpressionType.Equal -> Expr.Eq
            | ExpressionType.LessThan -> Expr.Lt
            | ExpressionType.LessThanOrEqual -> Expr.Lte
            | ExpressionType.GreaterThan -> Expr.Gt
            | ExpressionType.GreaterThanOrEqual -> Expr.Gte
            | ExpressionType.AndAlso -> Expr.And 
            | ExpressionType.OrElse -> Expr.Or
            | a -> failwithf "Unable to map %A to a binary op." a
        
        match e with 
        | :? System.Linq.Expressions.BinaryExpression as expr -> 
            let op = mapBinaryOperator expr.NodeType
            Some (op, expr.Left, expr.Right)
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

    let tupleToAnonType (ty:Type) = 
        let t = ty.GetGenericTypeDefinition()
        let mappedAnonType = tupleToAnonymousTypeMap.[t]
        mappedAnonType.MakeGenericType(ty.GenericTypeArguments)

    let map state (e:Expression) = 
        let rec walk state (e:Expression) = 
            printfn "Walking %A" e
            match e with 
            | MethodCall(None, (MethodWithName "Where"), [_; (Quote (Lambda (source, BinaryExpression(op, (PropertyGet l | Constant l), (PropertyGet r | Constant r)))))]) ->
                printfn "Where %A %A %A" op l r
                { state with Filter = (Some (source.[0].Type, Binary(op, l, r))) }
            | MethodCall(None, (MethodWithName "Select"), [_; (Quote (LambdaProjection (_, projs)))]) ->
                { state with Projections = projs |> List.map MemberAccess }
            | _ -> state

        walk state e

type QueryProvider(state, executor : (Type * Expr.Query) -> seq<obj>) =
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
            else failwithf "Unmatching types in binary expression %A %A" a b
        | Expr.Const (ty, _) -> ty

    let computeProjectedType (query:Expr.Query) = 
        match query.Projections with 
        | [] ->
            match query.Filter with
            | Some (t, _) -> t
            | None -> typeof<Unit>
        | [a] -> reduceType a
        | a -> 
             List.map reduceType a 
             |> List.toArray 
             |> FSharpType.MakeTupleType
             |> Expression.tupleToAnonType

    let toIQueryable (query:Expr.Query) =
        let returnType = computeProjectedType query
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
            let query = Expression.map state e 
            executor (computeProjectedType query, query)  |> box

        member x.Execute<'a>(e:Expression) : 'a =
            let query = Expression.map state e 
            executor (computeProjectedType query, query) |> unbox<'a>

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
            

         
      
// Put any utilities here
[<AutoOpen>]
module internal Utilities = 

    let x = 1

// Put any runtime constructs here
type DataSource(filename:string) = 
    member this.FileName = filename


// Put the TypeProviderAssemblyAttribute in the runtime DLL, pointing to the design-time DLL
[<assembly:CompilerServices.TypeProviderAssembly("QueryableProvider.DesignTime.dll")>]
do ()
