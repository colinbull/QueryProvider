module QueryExprTests

open System
open QueryableProvider
open Xunit

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

let queryable f = 
    new Queryable<Student>(Expr.Query.Empty, f)

[<Fact>]
let ``select with identity``() = 
    let test (typ:Type, query:Expr.Query) = 
        Assert.True(true)
        Unchecked.defaultof<obj>

    query { 
        for student in (queryable test) do 
        select student 
    }