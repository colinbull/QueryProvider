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

    
    type Join =
        { Source : QueryExpr 
          SourceKeyExpr : QueryExpr
          Dest : QueryExpr 
          DestKeyExpr : QueryExpr 
          Projection : Type list }

    and TypedExpr = 
        { Type : Type
          Expr : QueryExpr }

    and QueryExpr = 
        | Binary of BinOp * QueryExpr * QueryExpr
        | Unary of UnOp * QueryExpr
        | Const of Type * obj
        | MemberAccess of MemberInfo
        | MethodCall of MethodInfo * QueryExpr list
        | Scalar of QueryExpr
        | Vector of QueryExpr list
        | Sequence of QueryExpr list

     type Query = 
        { Grouping : TypedExpr option
          Joins : Join list
          Filter : TypedExpr option
          Projections : QueryExpr option }
        static member Empty = 
            { Filter = None; 
              Grouping = None;
              Joins = []
              Projections = None }

module Patterns = 

    let (|PropertyGet|_|) (e:Expression) = 
         match e with 
         | :? MemberExpression as me -> 
            Some(Expr.MemberAccess me.Member)
         | _ -> None 

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
        | PropertyGet e -> e
        | BinaryExpression(op, l, r) -> 
            Expr.Binary(op, map l, map r)
        | a -> failwithf "Could not map expression unsupported: %A" a

    let rec reduceType (expr:Expr.QueryExpr) = 
        match expr with
        | Expr.MethodCall(mi, _) -> 
            let returnType = mi.ReturnType 
            if returnType.IsGenericType && (returnType.GetGenericTypeDefinition() = typedefof<IQueryable<_>>)
            then returnType.GenericTypeArguments.[0]
            else returnType
        | Expr.MemberAccess ma ->
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

    let computeGroupingType (ty:TypedExpr) = 
        let groupingType = typedefof<Grouping<_,_>>
        let keyType = reduceType ty.Expr 
        groupingType.MakeGenericType([|keyType;ty.Type|])

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
                | [a] -> FSharpType.MakeTupleType (Array.ofList a.Projection) |> tupleToAnonType 
                | a -> failwithf "Only a single join projection %A supported for joins" a
            | Some a -> computeGroupingType a
        | Some a -> reduceType a  

    let mergeProjections (a:QueryExpr option) (b:QueryExpr option) = 
        match a, b with 
        | Some a, Some b -> Some(Sequence([a;b]))
        | Some a, _ -> Some(a)
        | _, Some b -> Some(b)
        | None, None -> None

    let translate state (e:Expression) = 
        let rec walk state (e:Expression) = 
            printfn "Walking %A" e
            match e with 
            | MethodCall(None, (MethodWithName "Where"), [_; (Quote (Lambda (source, e)))]) ->
                { state with Filter = Some({ Type = source.[0].Type; Expr = map e }) }
            | MethodCall(None, (MethodWithName "Join"), [Constant source; Constant dest; Quote (Lambda (_, sourceKeyExpr)); Quote (Lambda (_, destKeyExpr)); Quote (Lambda (projs, _))]) ->
                printfn "In Join %A %A %A %A %A" source dest sourceKeyExpr destKeyExpr projs
                let join = { Source = source; SourceKeyExpr = map sourceKeyExpr; Dest = dest; DestKeyExpr = map destKeyExpr; Projection = projs |> List.map (fun x -> x.Type) }
                { state with Joins = join :: state.Joins }
            | MethodCall(None, (MethodWithName "Select"), [_; (Quote (LambdaProjection (_, projs)))]) ->
                match projs with
                | [a] ->
                    { state with Projections = Some(Scalar(MemberAccess a)) }
                | projs -> 
                    { state with Projections = Some(Vector(projs |> List.map MemberAccess)) }
            | MethodCall(None, (MethodWithName "GroupBy"), [_; (Quote (Lambda (source, e)))]) ->
                { state with Grouping = Some({ Type = source.[0].Type; Expr = map e }) }
            | MethodCall(None, method, [_; (Quote (LambdaProjection (_, projs)))]) ->
                { state with Projections = mergeProjections state.Projections (Some(Scalar(MethodCall(method, projs |> List.map MemberAccess)))) }
            | MethodCall(None, method, args) ->
                { state with Projections = mergeProjections state.Projections (Some(Scalar(MethodCall(method, args.[1..] |> List.map map)))) }
            | _ -> state

        walk state e

type QueryProvider(state, executor : (Type * Expr.Query) -> obj) =
    let toIQueryable (query:Expr.Query) =
        printfn "ToIQueryable: %A" query
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
