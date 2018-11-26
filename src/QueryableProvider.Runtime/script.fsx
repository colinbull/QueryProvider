#load "QueryableProvider.Runtime.fs"

open QueryableProvider
open System
open System.Collections.Generic
open System.Linq.Expressions
open System.Linq



module ExampleImplementation = 

    open System.Reflection
    open Microsoft.FSharp.Reflection
    open Expr
    let getValue (q:Expr) = 
        match q with 
        | Const (t, o) -> (fun _ -> o)
        | Identity -> (fun o -> o)
        | MemberAccess ms ->
            ((fun x -> x), ms) 
            ||> List.fold (fun s ma -> 
                            match ma.MemberType with
                            | MemberTypes.Property | MemberTypes.Field -> 
                                (fun x -> ma.GetValue(x) |> s)
                            | MemberTypes.Method ->
                                let mi = (ma :?> MethodInfo)
                                (fun x ->
                                     if mi.IsStatic
                                     then (ma :?> MethodInfo).Invoke(null, [|x|])
                                     else (ma :?> MethodInfo).Invoke(x, null)
                                     |> s
                                )
                            | _ -> failwithf "Unable to invoke getvalue %A" ma
            )
        | a -> failwithf "Unable to get value from %A" a

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
            | "Select" -> (fun xs -> Enumerable.Select(unbox<_> xs, new Func<_,_>(getValue parameters.[0])) |> box)
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
        | Identity -> id
        | q -> raise(NotImplementedException(sprintf "%A projection is not implemented" q))

    let inline mkFilterFunc (q:TypedExpr) =  
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

        Seq.choose (fun x ->  if filterFunc x then Some(box x) else None)
 

    let cast (ty:Type) (o:obj) = 
        let input = Expression.Parameter(typeof<obj>, "data");
        let body = Expression.Convert(input, ty);
        let run = Expression.Lambda(body, input).Compile();

        run.DynamicInvoke([|o|])

    let inline mkGroupingFunc (a:TypedExpr) =
        let groupingFunc = getValue a.Expr
        let groupingTy = Expression.computeGroupingType a
        
        let ctor = groupingTy.GetConstructor([|groupingTy.GenericTypeArguments.[0]; typedefof<seq<_>>.MakeGenericType(groupingTy.GenericTypeArguments.[1])|])
        
        Seq.groupBy (fun x -> groupingFunc x)
        >> Seq.map (fun (key, items) -> ctor.Invoke([|key; box items|])) 

    let mkJoinFunc joins = 
        match joins with 
        | [] -> None
        | [j] -> 
            let outer = j.Dest |> function | Const (_, v) -> v | a -> failwithf "Unable to get constant value for join (outer) %A" a 
            // let inner = j.Source |> function | Const (_, v) -> (v |> unbox<seq<obj>>) | a -> failwithf "Unable to get constant value for join (inner) %A" a 
            let projectedType = FSharpType.MakeTupleType (Array.ofList j.Projection) |> Expression.tupleToAnonType 
             
            (fun (xs:seq<'a>) -> Enumerable.Join(unbox<'a> outer, xs, 
                                    new Func<_,_>(fun x -> getValue j.DestKeyExpr x), 
                                    new Func<_,_>(fun x -> getValue j.SourceKeyExpr x), 
                                    (fun x y -> Activator.CreateInstance(projectedType, [|y;x|])))
            )
            |> Some
        | a -> failwithf "Only a single join supported in this implementation"

    let inline execute<'a> (source:seq<'a>) (ty,query:Query) = 
        printfn "%A %A" source query

        let filter = 
            defaultArg (query.Filter |> Option.map mkFilterFunc) (fun x -> x)

        let projection : seq<'a> -> obj =
            defaultArg (query.Projections |> Option.map mkProjectionFunc) (fun x -> box x)

        match query.Grouping with 
        | Some grouping -> 
            source 
            |> filter 
            |> mkGroupingFunc grouping
            |> projection
        | None -> 
            source 
            |> filter 
            |> projection

type Student = 
    { StudentId : int
      Name : string
      Age : int
      Grade : float }

type CourseEnrollment = 
    { Id : int 
      StudentId : int 
      CourseId : int }

type Course = 
    { CourseId: int 
      CourseName : string }

let courses = [
    { CourseId = 1; CourseName = "Introduction to F#" }
    { CourseId = 2; CourseName = "Introduction to Functional Programming" }
    { CourseId = 3; CourseName = "Queryable and Typeproviders" }
]

let courseEnrollment = [
    { Id = 1; StudentId = 1; CourseId = 1}
    { Id = 2; StudentId = 1; CourseId = 2}
    { Id = 3; StudentId = 2; CourseId = 2}
    { Id = 4; StudentId = 2; CourseId = 3}
    { Id = 5; StudentId = 3; CourseId = 1}
    { Id = 6; StudentId = 3; CourseId = 2}
    { Id = 7; StudentId = 3; CourseId = 3}
]

let students = [
    { StudentId = 1; Name = "Tom"; Age = 21; Grade = 1. }
    { StudentId = 2; Name = "Dave"; Age = 21; Grade = 2. }
    { StudentId = 3; Name = "Anna"; Age = 22; Grade = 3. }
    { StudentId = 4; Name = "Sophie"; Age = 21; Grade = 4. }
    { StudentId = 5; Name = "Richard"; Age = 20; Grade = 6. }
    { StudentId = 5; Name = "Richard"; Age = 20; Grade = 6. }
]

let studentQueryable = new Queryable<Student>(Expr.Query.Empty, ExampleImplementation.execute students)
let courseQueryable = new Queryable<Course>(Expr.Query.Empty, ExampleImplementation.execute courses)
let courseEnrollmentQueryable = new Queryable<CourseEnrollment>(Expr.Query.Empty, ExampleImplementation.execute courseEnrollment)


let studentProjection = 
    query { 
        for student in studentQueryable do
        groupBy student.Age into g
        select (g.Key, g.Count())
    } |> Seq.toArray