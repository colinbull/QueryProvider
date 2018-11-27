namespace QueryableProvider

open System
open System.Linq
open System.Linq.Expressions
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
          Projection : (Type list * Expr) }

    and TypedExpr = 
        { Type : Type
          Expr : Expr }

    and Expr = 
        | Binary of BinOp * Expr * Expr
        | Unary of UnOp * Expr
        | Const of Type * obj
        | MemberAccess of MemberInfo list
        | MethodCall of MethodInfo * Expr list
        | New of Type * Expr list
        | Scalar of Expr
        | Vector of Expr list
        | Sequence of Expr list
        | Parameter of Type * string  

     type Query = 
        { Grouping : TypedExpr option
          Joins : Join list
          Filter : TypedExpr option
          Projections : Expr option }
        static member Empty = 
            { Filter = None; 
              Grouping = None;
              Joins = []
              Projections = None }

module Patterns = 

    let rec map (e:Expression) = 
        match e with 
        | :? ParameterExpression as p -> Expr.Parameter(p.Type, p.Name) 
        | Constant e -> e
        | MemberAccess e -> e
        | BinaryExpression(op, l, r) -> 
            Expr.Binary(op, map l, map r)
        | New (ty, expr) -> 
            Expr.New (ty, expr)
        | Quote (Lambda (_,e)) -> map e
        | a -> failwithf "Could not map expression unsupported: %A - type: %A" a a.NodeType

    and (|MemberAccess|_|) (e:Expression) = 
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
        | a -> Some (a |> Expr.MemberAccess)

    and (|Constant|_|) (e:Expression) =
        match e with
        | :? ConstantExpression as ce -> Some(Expr.Const(ce.Type, ce.Value))
        | _ -> None

    and (|MethodCall|_|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Call, (:? MethodCallExpression as e) -> 
            Some ((match e.Object with null -> None | obj -> Some obj), e.Method, Seq.toList e.Arguments)
        | _ -> None

    and (|MethodWithName|_|)   (s:string) (m:MethodInfo)   = if s = m.Name then Some () else None
    and (|PropertyWithName|_|) (s:string) (m:PropertyInfo) = if s = m.Name then Some () else None

    and (|Quote|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Quote, (:? UnaryExpression as ce) ->  ce.Operand
        | _ -> e

    and (|New|_|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.New, (:? NewExpression as ne) ->
                let projectionMap = 
                    ne.Arguments 
                    |> Seq.fold (fun s a -> 
                         match a with
                         | MemberAccess a -> 
                            a :: s
                         | MethodCall (_, mi, parms)  -> 
                            Expr.MethodCall (mi, parms |> List.map map) :: s
                         | :? ParameterExpression -> s  
                         | _ -> failwithf "Unknown expression in new Type: %A" a.NodeType
                    ) ([])
                Some (e.Type, projectionMap |> List.rev)
        | _ -> None

    and (|Lambda|_|) (e:Expression) = 
        match e.NodeType, e with 
        | ExpressionType.Lambda, (:? LambdaExpression as ce) ->  Some (Seq.toList ce.Parameters, ce.Body)
        | _ -> None

    and (|LambdaProjection|_|) (e:Expression) =
        match e with
        | Lambda (sourceType::_, body) ->
            match body with
            | MemberAccess a -> 
                Some a
            | New (_, a) -> 
                Some (Expr.Vector a)            
            | _ -> None
        | _ -> None

    and (|BinaryExpression|_|) (e:Expression) =
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

    let anonTypeToTupleMap = 
        let dict = new Dictionary<Type,Type>()
        for (tupleTy,anonTy) in tupleTypes do dict.[tupleTy] <- anonTy
        dict    

    let tupleToAnonType (ty:Type) = 
        let t = ty.GetGenericTypeDefinition()
        let mappedAnonType = tupleToAnonymousTypeMap.[t]
        mappedAnonType.MakeGenericType(ty.GenericTypeArguments)

    let anonTypeToTupleType (ty:Type) =
        let t = ty.GetGenericTypeDefinition()
        let mappedTupleType = tupleToAnonymousTypeMap.[t]
        mappedTupleType.MakeGenericType(ty.GenericTypeArguments)


    let getTypeOrQueryableType (e:Expression) = 
        let returnType = e.Type
        if returnType.IsGenericType && (returnType.GetGenericTypeDefinition() = typedefof<IQueryable<_>>)
        then returnType.GenericTypeArguments.[0]
        else returnType

    let unwrapGenericArgsOrType (e:Expression) = 
        let returnType = e.Type
        if returnType.IsGenericType && 
           ((returnType.GetGenericTypeDefinition() = typedefof<IQueryable<_>>) 
            || (tupleTypes |> Array.exists (fun (_,x) -> x = returnType.GetGenericTypeDefinition()))) 
        then returnType.GenericTypeArguments
        else [|returnType|]

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
        | Expr.New (ty, _) -> ty 
        | Parameter(ty, _) -> ty

    let computeGroupingType (ty:TypedExpr) = 
        let groupingType = typedefof<Grouping<_,_>>
        let keyType = reduceType ty.Expr 
        groupingType.MakeGenericType([|keyType;ty.Type|])

    let computeJoinType (joins:Join list) = 
        let joinTypes = 
            [  let d = new Dictionary<Type, obj>() 
               for { Projection = (j, _) } in joins do
                  for p in j do 
                     if not(d.ContainsKey(p))
                     then yield p 
            ]
        FSharpType.MakeTupleType (Array.ofList joinTypes) |> tupleToAnonType 

    let computeProjectedType (query:Expr.Query) = 
        match query.Projections with 
        | None ->
            match query.Grouping with
            | None ->
                match query.Joins with 
                | [] -> 
                    match query.Filter with 
                    | None -> typeof<Unit> 
                    | Some a -> a.Type
                | a -> computeJoinType a
            | Some a -> computeGroupingType a
        | Some a -> reduceType a  

    let mergeProjections (a:Expr option) (b:Expr option) = 
        match a, b with 
        | Some a, Some b -> Some(Sequence([a;b]))
        | Some a, _ -> Some(a)
        | _, Some b -> Some(b)
        | None, None -> None

    let translate state (e:Expression) =
        let rec walk state (e:Expression) = 
            match e with 
            | MethodCall(None, (MethodWithName "Where"), [_; (Quote (Lambda (source, e)))] as a) ->
                { state with Filter = Some({ Type = source.[0].Type; Expr = map e }) }
            | MethodCall(None, (MethodWithName "Join"), [Constant source; Constant dest; Quote (Lambda (_, sourceKeyExpr)); Quote (Lambda (_, destKeyExpr)); Quote (Lambda (projs, e))]) ->
                let join = { Source = source; SourceKeyExpr = map sourceKeyExpr; Dest = dest; DestKeyExpr = map destKeyExpr; Projection = (projs |> Seq.collect unwrapGenericArgsOrType |> Seq.toList, map e) }
                { state with Joins = state.Joins @ [join] }
            | MethodCall(None, (MethodWithName "Select"), [_; (Quote (LambdaProjection proj))]) ->
                { state with Projections = Some(proj) }
            | MethodCall(None, (MethodWithName "GroupBy"), [_; (Quote (Lambda (source, e)))]) ->
                { state with Grouping = Some({ Type = source.[0].Type; Expr = map e }) }
            | MethodCall(None, method, [_; (Quote (LambdaProjection proj))]) ->
                { state with Projections = mergeProjections state.Projections (Some(proj)) }
            | MethodCall(None, method, args) ->
                { state with Projections = mergeProjections state.Projections (Some(Scalar(MethodCall(method, args.[1..] |> List.map map)))) }
            | _ -> state
        walk state e

type QueryProvider(state, executor : (Type * Expr.Query) -> obj) =
    let toIQueryable ty (query:Expr.Query) =
        let ty = typedefof<Queryable<_>>.MakeGenericType([|ty|])
        ty.GetConstructors().[0].Invoke([|query; executor|]) :?> IQueryable
    
    interface IQueryProvider with
        member x.CreateQuery(e:Expression) : IQueryable =
            Expression.translate state e 
            |> toIQueryable (Expression.getTypeOrQueryableType e)

        member x.CreateQuery<'T>(e:Expression) : IQueryable<'T> = 
            Expression.translate state e 
            |> toIQueryable (Expression.getTypeOrQueryableType e) 
            :?> IQueryable<'T>
            
        member x.Execute(e:Expression) : obj =
            let query = Expression.translate state e 
            executor ((Expression.computeProjectedType query), query)  |> box

        member x.Execute<'a>(e:Expression) : 'a =
            let query = Expression.translate state e 
            executor ((Expression.computeProjectedType query), query) |> unbox<'a>

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
