#load "QueryableProvider.Runtime.fs"

open MyNamespace
open System
open System.Linq

module ExampleImplementation = 

    open Expr
    
    let getValue (q:QueryExpr) = 
        match q with 
        | Const (t, o) -> (fun _ -> o)
        | MemberAccess ma -> ma.GetValue
        | a -> failwithf "Unable to get value from %A" a

    let rec mkFunc (ty:Type) (q:QueryExpr) : (obj -> obj) =
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
            | a -> id
        | Scalar a -> (fun xs -> box(seq { for x in xs |> unbox<seq<obj>> do yield getValue a x }))  
        | Vector a ->
            let projected = a |> List.map getValue 
            (fun xs -> box(seq {
                for x in xs |> unbox<seq<obj>> do 
                    yield Activator.CreateInstance(ty, [| for projection in projected -> (projection x)|]) 
             }))
        | Sequence stmts ->
             (fun xs -> 
                 let f = 
                     stmts
                     |> Seq.fold (fun (prev:(obj -> obj) option) (x:QueryExpr) ->
                         let next = (mkFunc ty x)
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
        | q -> (fun xs -> box(seq { for x in xs |> unbox<seq<obj>> do yield box x }))

    let mkFilterFunction (q:Query) = 
        match q.Filter with 
        | None -> (fun _ -> true)
        | Some (_, x) -> 
            let rec walkExpr (q:QueryExpr) = 
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
            walkExpr x
            
    let rec mkProjectionFunction (ty:Type) (q:Query) = 
        match q.Projections with 
        | Some a -> mkFunc ty a
        | q -> (fun xs -> box(seq { for x in xs do yield box x }))

    let execute source (ty,query) = 
        printfn "%A" query
        let projection = mkProjectionFunction ty query 
        let filter = mkFilterFunction query
        source |> Seq.filter filter |> projection     
 

type Student = {
    StudentId : int
    Name : string
    Age : int
    Grade : float 
}
let students = [
    { StudentId = 1; Name = "Tom"; Age = 21; Grade = 1. }
    { StudentId = 2; Name = "Dave"; Age = 21; Grade = 2. }
    { StudentId = 3; Name = "Anna"; Age = 22; Grade = 3. }
    { StudentId = 4; Name = "Sophie"; Age = 21; Grade = 4. }
    { StudentId = 5; Name = "Richard"; Age = 20; Grade = 6. }
    { StudentId = 5; Name = "Richard"; Age = 20; Grade = 6. }
]

let q = new Queryable<Student>(Expr.Query.Empty, ExampleImplementation.execute students)


let sudentProjection = 
    query { 
        for student in q do
        groupBy student.Age into g 
        select (g.Key, g.Count())
    } |> Seq.toArray