#load "QueryableProvider.Runtime.fs"

open MyNamespace
open System
open System.Reflection


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
   

let q = new Queryable<Student>(Expr.Query.Empty, fun (ty, q) -> 
    printfn "%A" q
    let projection = Expr.preComputeProjectionExpression ty q 
    let filter = Expr.preComputeFilterExpression q
    seq{
        for s in students |> Seq.filter filter do 
            yield projection s     
    } 
)

let sudentProjection = 
    query { 
        for student in q do
        where (student.Age = 20)
        select (student.Name, student.Age, student.StudentId)
    } |> Seq.toArray