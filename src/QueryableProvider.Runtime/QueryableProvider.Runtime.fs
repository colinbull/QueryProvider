namespace QueryableProvider

open System
open System.Linq
open System.Linq.Expressions
open System.Collections
open System.Collections.Generic
open System.Reflection
open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Linq.RuntimeHelpers
open System.Runtime.CompilerServices

[<AutoOpen>]
module Extensions = 

    type MemberInfo with 

    [<Extension>]
    member ma.GetValue(a:obj) =
        try
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
        with 
            | :? TargetException as te -> 
                raise(new TargetException(sprintf "Target:%A does not match %A" (a.GetType()) ma.DeclaringType))

    
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

    
    type Join =
        { Source : Expr 
          SourceKeyExpr : Expr
          Dest : Expr 
          DestKeyExpr : Expr 
          Projection : Type list }

    and TypedExpr = 
        { Type : Type
          Expr : Expr }

    and Expr = 
        | Binary of BinOp * Expr * Expr
        | Unary of UnOp * Expr
        | Const of Type * obj
        | MemberAccess of MemberInfo list
        | MethodCall of MethodInfo * Expr list
        | Scalar of Expr
        | Vector of Expr list
        | Sequence of Expr list
        | Identity

    and QueryExpr = 
        | Projection of Expr
        | Filter of TypedExpr 
        | Join of Join 
        | Grouping of TypedExpr 

     type Query = QueryExpr list

module Patterns = 

    let (|MemberAccess|_|) (e:Expression) = 
        let rec walkAccess state (e:Expression) =
             match e with 
             | :? MemberExpression as me -> 
                let newState = me.Member :: state
                if not(isNull me.Expression) 
                then walkAccess newState me.Expression
                else newState
             | _ -> state
        match walkAccess [] e with
        | [] -> None 
        | a -> Some (a |> List.rev |> Expr.MemberAccess)

    let (|Constant|_|) (e:Expression) =
        match e with
        | :? ConstantExpression as ce -> Some(Expr.Const(ce.Type, ce.Value))
        | _ -> None

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
                         | ExpressionType.Call, (:? MethodCallExpression as e)  -> 
                            (e.Method :> MemberInfo) :: s
                         | _, _ -> failwithf "Unknown expression in new Type: %A" a.NodeType
                    ) ([])
                Some (body.Type, projectionMap |> List.rev)
            | _, _ -> None
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

    let rec map (e:Expression) = 
        match e with 
        | Constant e -> e
        | MemberAccess e -> e
        | BinaryExpression(op, l, r) -> 
            Expr.Binary(op, map l, map r)
        | Quote (Lambda (_,e)) ->
            match e with 
            | :? ParameterExpression as pe -> Expr.Identity
            | _ -> failwithf "Unable to map quoted lambda: %A - type: %A" e e.NodeType
        | a -> failwithf "Could not map expression unsupported: %A - type: %A" a a.NodeType

    let rec reduceType expr = 
        match expr with
        | Expr.MethodCall(mi, _) -> 
            let returnType = mi.ReturnType 
            if returnType.IsGenericType && (returnType.GetGenericTypeDefinition() = typedefof<IQueryable<_>>)
            then returnType.GenericTypeArguments.[0]
            else returnType
        | Expr.MemberAccess ma ->
            let ma = ma |> List.last
            match ma.MemberType with 
            | MemberTypes.Property -> (ma :?> PropertyInfo).PropertyType
            | MemberTypes.Method -> (ma :?> MethodInfo).ReturnType
            | MemberTypes.Field -> (ma :?> FieldInfo).FieldType
            | a -> failwithf "Unable to reduce type %A" a
        | Expr.Unary (_,a) -> reduceType a
        | Expr.Binary (op, a, b) as expr ->
            let aTy, bTy = reduceType a, reduceType b 
            if aTy = bTy 
            then aTy 
            else failwithf "Unmatching types in binary expression %A %A %A" expr aTy bTy
        | Expr.Const (ty, _) -> ty
        | Expr.Scalar s -> reduceType s
        | Expr.Vector s ->
             List.map reduceType s 
             |> List.toArray 
             |> FSharpType.MakeTupleType
             |> tupleToAnonType
        | Sequence ss -> 
            ss |> Seq.last |> reduceType
        | Expr.Identity -> typedefof<_>

    let computeGroupingType (ty:TypedExpr) = 
        let groupingType = typedefof<Grouping<_,_>>
        let keyType = reduceType ty.Expr 
        groupingType.MakeGenericType([|keyType;ty.Type|])

    let computeProjectedType (query:Expr.Query) = 
        match query with 
        | [] -> typeof<Unit> 
        | h :: _ -> 
            match h with 
            | Projection a -> reduceType a 
            | Filter a -> a.Type  
            | Grouping a -> computeGroupingType a 
            | Join a -> FSharpType.MakeTupleType (Array.ofList a.Projection) |> tupleToAnonType 
 

    let mergeProjections (a:QueryExpr) (b:QueryExpr) = 
        match a, b with 
        | Projection a, Projection b -> Projection(Sequence([a;b]))
        | _, _ -> failwithf "Both expressions must be a projection to merge"

    let translate state (e:Expression) = 
        let rec walk state (e:Expression) = 
       //     printfn "Walking %A" e
            match e with 
            | MethodCall(None, (MethodWithName "Where"), [_; (Quote (Lambda (source, e)))] as a) ->
                Filter ({ Type = source.[0].Type; Expr = map e }) :: state
            | MethodCall(None, (MethodWithName "Join"), [Constant source; Constant dest; Quote (Lambda (_, sourceKeyExpr)); Quote (Lambda (_, destKeyExpr)); Quote (Lambda (projs, _))]) ->
                let join = { Source = source; SourceKeyExpr = map sourceKeyExpr; Dest = dest; DestKeyExpr = map destKeyExpr; Projection = projs |> List.map (fun x -> x.Type) }
                Join (join) :: state
            | MethodCall(None, (MethodWithName "Select"), [_; (Quote (LambdaProjection (_, projs)))]) ->
                match projs with
                | [a] ->
                    Projection(Scalar(MemberAccess [a])) :: state 
                | projs -> 
                    Projection(Vector(projs |> List.map (fun x -> MemberAccess[x]))) :: state
            | MethodCall(None, (MethodWithName "GroupBy"), [_; (Quote (Lambda (source, e)))]) ->
                QueryExpr.Grouping({ Type = source.[0].Type; Expr = map e }) :: state
            | MethodCall(None, method, [_; (Quote (LambdaProjection (_, projs)))]) ->
                mergeProjections state.Head (Projection(Scalar(MethodCall(method, projs |> List.map (fun x -> MemberAccess[x]))))) :: state.Tail 
            | MethodCall(None, method, args) ->
                mergeProjections state.Head (Projection(Scalar(MethodCall(method, args.[1..] |> List.map map)))) :: state.Tail
            | _ -> state

        walk state e

type QueryProvider(state, executor : (Type * Expr.Query) -> obj) =
    let toIQueryable (query:Expr.Query) =
        let returnType = Expression.computeProjectedType query
        let ty = typedefof<Queryable<_>>.MakeGenericType(returnType)
        ty.GetConstructors().[0].Invoke([|query; executor|]) :?> IQueryable
    
    interface IQueryProvider with
        member x.CreateQuery(e:Expression) : IQueryable =
            Expression.translate state e 
            |> toIQueryable

        member x.CreateQuery<'T>(e:Expression) : IQueryable<'T> = 
            Expression.translate state e 
            |> toIQueryable  
            :?> IQueryable<'T>
            
        member x.Execute(e:Expression) : obj =
            let query = Expression.translate state e 
            executor (Expression.computeProjectedType query, query)  |> box

        member x.Execute<'a>(e:Expression) : 'a =
            let query = Expression.translate state e 
            executor (Expression.computeProjectedType query, query) |> unbox<'a>

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
