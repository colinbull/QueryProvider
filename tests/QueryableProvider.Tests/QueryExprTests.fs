module QueryExprTests

open System
open QueryableProvider
open Xunit

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

let studentQueryable = new Queryable<Student>(Expr.Query.Empty, QueryableObjectImpl.execute students)
let courseQueryable = new Queryable<Course>(Expr.Query.Empty, QueryableObjectImpl.execute courses)
let courseEnrollmentQueryable = new Queryable<CourseEnrollment>(Expr.Query.Empty, QueryableObjectImpl.execute courseEnrollment)

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