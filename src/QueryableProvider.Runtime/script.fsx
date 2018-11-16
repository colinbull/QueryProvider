#load "QueryableProvider.Runtime.fs"

open MyNamespace
open System
open System.Reflection

module ExampleImplementation = 

    open System
    open System.Linq
    open System.Linq.Expressions
    open System.Reflection
    open System.Collections
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
            | "Sum" -> (fun xs -> Convert.ChangeType(xs |> unbox<seq<obj>> |> Seq.sumBy (fun x -> unbox<float>(getValue parameters.[0] x)), ty))
            | "Contains" ->
                let konst = (getValue parameters.[0]) Unchecked.defaultof<obj>
                (fun xs -> xs |> unbox<seq<obj>> |> Seq.contains (unbox<_> konst) |> box)
            | a -> (fun x -> box(seq { yield Activator.CreateInstance(ty) }))
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
}
let students = [
    { StudentId = 1; Name = "Tom"; Age = 21 }
    { StudentId = 2; Name = "Dave"; Age = 21 }
    { StudentId = 3; Name = "Anna"; Age = 22 }
    { StudentId = 4; Name = "Sophie"; Age = 21 }
    { StudentId = 5; Name = "Richard"; Age = 20 }
]

let q = new Queryable<Student>(Expr.Query.Empty, ExampleImplementation.execute students)





let sudentProjection = 
    query { 
        for student in q do
        where (student.Age = 21)
        select student.Age
        contains 21
    }