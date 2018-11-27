namespace QueryableProvider

module QueryableObjectImpl =

    open System
    open System.Collections.Generic
    open System.Linq.Expressions
    open System.Linq
    open System.Reflection
    open Microsoft.FSharp.Reflection
    open Expr

    let getValue (q:Expr) = 
        let invoke s (ma:MemberInfo) =    
            match ma.MemberType with
            | MemberTypes.Property | MemberTypes.Field -> 
                (fun x -> 
                    let tgt = s x 
                    printfn "Property target: %s %A" ma.Name tgt
                    ma.GetValue(tgt))
            | MemberTypes.Method ->
                let mi = (ma :?> MethodInfo)
                (fun x ->
                     let x = s x
                     if mi.IsStatic
                     then (ma :?> MethodInfo).Invoke(null, [|x|])
                     else (ma :?> MethodInfo).Invoke(x, null)
                )
            | _ -> failwithf "Unable to invoke getvalue %A" ma
        
        match q with 
        | Const (t, o) -> (fun _ -> o)
        | Parameter _ -> (fun o -> o)
        | MemberAccess ms ->
            printfn "Member Access: %A" ms
            ((fun x -> x), ms) 
            ||> List.fold (fun s ma -> printfn "Invoking:  %A" ma; invoke s ma)
        | MethodCall (mi,_) -> 
            (fun x -> (invoke (fun _ -> x) mi) x)
        | a -> failwithf "Unable to get value from %A" a

    let cast (ty:Type) (o:obj) = 
        let input = Expression.Parameter(typeof<obj>, "data");
        let body = Expression.Convert(input, ty);
        let run = Expression.Lambda(body, input).Compile();

        run.DynamicInvoke([|o|])

    let attemptUnpackObject (o:obj) = 
        let ty = o.GetType() 
        if ty.IsGenericType
        then 
            let args = ty.GenericTypeArguments
            args |> Array.mapi (fun i t -> ty.GetProperty(sprintf "Item%d" (i + 1)).GetValue(o))
        elif isNull o
        then [||] 
        else [|o|]

    let rec mkProjectionFunc (q:Expr) : (obj -> obj) =
        match q with  
        | Scalar (MethodCall (method, parameters)) -> 
            match method.Name with 
            | "Sum" -> 
                (fun xs -> 
                    let value = xs |> unbox<seq<obj>> |> Seq.sumBy (fun x -> unbox<float>(Convert.ChangeType(getValue parameters.[0] x, typeof<float>)))
                    Convert.ChangeType(value, Expression.reduceType parameters.[0]) 
                )
            | "Average" ->
                (fun xs -> 
                    let value = xs |> unbox<seq<obj>> |> Seq.averageBy (fun x -> unbox<float>(Convert.ChangeType(getValue parameters.[0] x, typeof<float>)))
                    Convert.ChangeType(value, Expression.reduceType parameters.[0]) 
                )
            | "Min" -> 
                (fun xs -> 
                    let selector = getValue parameters.[0]
                    let value = xs |> unbox<seq<obj>> |> Seq.minBy (fun x -> unbox<float>(Convert.ChangeType(selector x, typeof<float>)))
                    Convert.ChangeType(selector value, Expression.reduceType parameters.[0]) 
                )
            | "Max" -> 
                (fun xs -> 
                    let selector = getValue parameters.[0]
                    let value = xs |> unbox<seq<obj>> |> Seq.maxBy (fun x -> unbox<float>(Convert.ChangeType(selector x, typeof<float>)))
                    Convert.ChangeType(selector value, Expression.reduceType parameters.[0]) 
                )
            | "Skip" ->
                let konst = unbox<int> ((getValue parameters.[0]) Unchecked.defaultof<obj>)
                (fun xs -> Enumerable.Skip(unbox<_> xs, konst) |> box)
            | "Take" ->
                let konst = unbox<int> ((getValue parameters.[0]) Unchecked.defaultof<obj>)
                (fun xs -> Enumerable.Take(unbox<_> xs, konst) |> box)
            | "Contains" ->
                let konst = (getValue parameters.[0]) Unchecked.defaultof<obj>
                (fun xs -> Enumerable.Contains(unbox<_> xs, konst) |> box)
            | "ElementAt" ->
                let konst = unbox<int> ((getValue parameters.[0]) Unchecked.defaultof<obj>)
                (fun xs -> Enumerable.ElementAt(unbox<_> xs, konst) |> box)   
            | "Count" -> (fun xs -> Enumerable.Count(unbox<_> xs) |> box)
            | "First" -> (fun xs -> Enumerable.First(unbox<_> xs) |> box)
            | "FirstOrDefault" -> (fun xs -> Enumerable.FirstOrDefault(unbox<_> xs) |> box)
            | "Last" -> (fun xs -> Enumerable.Last(unbox<_> xs) |> box)
            | "LastOrDefault" -> (fun xs -> Enumerable.LastOrDefault(unbox<_> xs) |> box)
            | "Single" -> (fun xs -> Enumerable.Single(unbox<_> xs) |> box)
            | "SingleOrDefault" -> (fun xs -> Enumerable.SingleOrDefault(unbox<_> xs) |> box) 
            | "Distinct" -> (fun xs -> Enumerable.Distinct(unbox<_> xs) |> box) 
            | "Select" -> (fun xs -> Enumerable.Select(unbox<_> xs, new Func<_,_>(fun x -> getValue parameters.[0])) |> box)
            | a -> raise(NotImplementedException(sprintf "scalar projection %A is not implemented" a))
        | Scalar a -> (fun xs -> box(seq { for x in xs |> unbox<seq<obj>> do yield getValue a x }))  
        | Vector a as x ->
            let projected = a |> List.map getValue
            
            let projectedType = Expression.reduceType x               
            (fun xs -> box(seq {
                for x in xs |> unbox<seq<obj>> do
                    let ps = [| for projection in projected -> (projection x)|]
                    yield Activator.CreateInstance(projectedType, ps) 
             }))
        | Sequence stmts ->
             (fun xs -> 
                 let f = 
                     stmts
                     |> Seq.fold (fun (prev:(obj -> obj) option) (x:Expr) ->
                         let next = (mkProjectionFunc x)
                         (fun xss ->
                             match prev with
                             | Some prev -> next (prev xss)
                             | None -> next xss
                         ) |> Some
                     ) None
                 match f with
                 | Some f ->
                     let r = (f xs)
                     r
                 | None -> box xs
             )
        | Const (t,c) -> (fun _ -> box(seq { yield c }))
        | Parameter _ -> id
        | q -> raise(NotImplementedException(sprintf "%A projection is not implemented" q))

    let mkFilterFunc (q:TypedExpr) =  
        let rec walkExpr (q:Expr) = 
            match q with
            | Binary(op, x ,y) -> 
                match op with 
                | Eq -> (fun s -> (getValue x s) = (getValue y s))
                | Gt -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) > 0))
                | Lt -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) < 0))
                | Gte -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) >= 0))
                | Lte -> (fun s -> (Unchecked.compare (getValue x s) (getValue y s) <= 0))
                | And -> (fun s -> (walkExpr x s) && (walkExpr y s))
                | Or -> (fun s -> (walkExpr x s) || (walkExpr y s))
            | _ -> failwithf "%A not supported for filter expressions" q
        let filterFunc = walkExpr q.Expr

        Seq.filter (filterFunc)
 

    let mkGroupingFunc (a:TypedExpr) =
        let groupingFunc = getValue a.Expr
        let groupingTy =  Expression.computeGroupingType a    
        let ctor = groupingTy.GetConstructor([|groupingTy.GenericTypeArguments.[0]; typedefof<seq<_>>.MakeGenericType(groupingTy.GenericTypeArguments.[1])|])
        
        Seq.groupBy (fun x -> groupingFunc x)
         >> Seq.map (fun (key, items) -> ctor.Invoke ([|key; items |])) 

    let rec mkJoinFunc joins = 
        let mutable f = None 
        for j in joins do 
            let outer = j.Dest |> function | Const (_, v) -> v :?> IEnumerable<_> | a -> failwithf "Unable to get constant value for join (outer) %A" a 
            let inner = j.Source |> function | Const (_, v) -> v :?> IEnumerable<_> | a -> failwithf "Unable to get constant value for join (inner) %A" a 
            let projectedType = FSharpType.MakeTupleType (Array.ofList (fst j.Projection)) |> Expression.tupleToAnonType 
            let ff = f 
            f <- Some (fun xs -> 
                        Enumerable.Join(outer, inner, 
                                           new Func<_,_>(fun x -> getValue j.DestKeyExpr x), 
                                           new Func<_,_>(fun x -> getValue j.SourceKeyExpr x), 
                                           (fun x y -> 
                                                let args = Array.append (attemptUnpackObject y) (attemptUnpackObject x)
                                                Activator.CreateInstance(projectedType, args)))
                                        :> seq<_>
                  )
        
        match f with 
        | Some f -> f 
        | None -> fun xs -> xs

    let execute (source:seq<'a>) (ty,query:Query) = 
        match query.Grouping, query.Joins with 
        | None, [] -> 
            source 
            |> defaultArg (query.Filter |> Option.map mkFilterFunc) (fun x -> x) 
            |> defaultArg (query.Projections |> Option.map mkProjectionFunc) (fun x -> box x)
        | None, joins ->
            source
            |> Seq.map box 
            |> mkJoinFunc joins
            |> defaultArg (query.Filter |> Option.map mkFilterFunc) (fun x -> x) 
            |> defaultArg (query.Projections |> Option.map mkProjectionFunc) (fun x -> box x) 
        | Some grouping, [] -> 
            source
            |> defaultArg (query.Filter |> Option.map mkFilterFunc) (fun x -> x) 
            |> mkGroupingFunc grouping
            |> defaultArg (query.Projections |> Option.map mkProjectionFunc) (fun x -> box x)
        | Some grouping, joins -> 
            source 
            |> Seq.map box 
            |> mkJoinFunc joins
            |> defaultArg (query.Filter |> Option.map mkFilterFunc) (fun x -> x) 
            |> mkGroupingFunc grouping
            |> defaultArg (query.Projections |> Option.map mkProjectionFunc) (fun x -> box x)
        