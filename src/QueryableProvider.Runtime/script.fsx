#load "QueryableProvider.Runtime.fs"

open MyNamespace
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

let applyProjection (ma:MemberInfo) (a:obj) = 
    match ma.MemberType with 
    | MemberTypes.Property -> (ma :?> PropertyInfo).GetValue(a)
    | MemberTypes.Method -> (ma :?> MethodInfo).Invoke(a, [||]) 
    | MemberTypes.Field -> (ma :?> FieldInfo).GetValue(a)
    | a -> failwithf "Unable to reduce type %A" a

let q = new Queryable<Student>(Expr.Query.Empty, fun q -> 
    printfn "%A" q
    let t = 
        q.Projections 
        |> List.map (function 
                     | Expr.MemberAccess ma -> 
                        fun x -> System.Convert.ChangeType(applyProjection ma x, typeof<int>) 
                     | a -> failwithf "Unknown %A" a)
    seq{
        for s in students do 
            for p in t do 
                yield (p s)
    } 
)

let sudentProjection = 
    query { 
        for student in q do
        where (student.Age = 20)
        select student.Age
    } |> Seq.toArray