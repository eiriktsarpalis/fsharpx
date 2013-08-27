namespace FSharpx.Core.Tests

module ReflectionTests =
    
    open System
    open System.Reflection
    
    open NUnit.Framework
    open Microsoft.FSharp.Reflection
    open FSharpx.Reflection

    open FsUnit

    //
    //  test code
    //

    type UnionTester =
        static member TestConstructor(u : 'Union, ?bindingFlags) =
            let uci, values = FSharpValue.GetUnionFields(u, typeof<'Union>, ?bindingFlags = bindingFlags)

            let ctor = FSharpValue.PreComputeUnionConstructorFast(typeof<'Union>, ?bindingFlags = bindingFlags)
            let result = ctor (uci.Tag, values)
            if obj.ReferenceEquals(u, null) then Assert.IsNull result
            else
                Assert.IsInstanceOf<'Union> result
                result :?> 'Union |> should equal u

        static member TestReader(u : 'Union, ?bindingFlags) =
            let actualUci, actualValues = FSharpValue.GetUnionFields(u, typeof<'Union>, ?bindingFlags = bindingFlags)

            let reader = FSharpValue.PreComputeUnionReaderFast(typeof<'Union>, ?bindingFlags = bindingFlags)
            let uci, values = reader u
            uci |> should equal actualUci
            values |> should equal actualValues

        static member TestTagReader(u : 'Union, ?bindingFlags) =
            let actualTag = FSharpValue.PreComputeUnionTagReader(typeof<'Union>, ?bindingFlags = bindingFlags) (u :> _)

            let tag = FSharpValue.PreComputeUnionTagReaderFast(typeof<'Union>, ?bindingFlags = bindingFlags) (u :> _)
            tag |> should equal actualTag


    type RecordTester =
        static member TestConstructor(r : 'Record, ?bindingFlags) =
            let fields = FSharpValue.GetRecordFields(r, ?bindingFlags = bindingFlags)

            let ctor = FSharpValue.PreComputeRecordConstructorFast(typeof<'Record>, ?bindingFlags = bindingFlags)
            let result = ctor fields 
            Assert.IsInstanceOf<'Record> result
            result :?> 'Record |> should equal r

        static member TestReader(r : 'Record, ?bindingFlags) =
            let actualValues = FSharpValue.GetRecordFields(r, ?bindingFlags = bindingFlags)

            let reader = FSharpValue.PreComputeRecordReaderFast(typeof<'Record>, ?bindingFlags = bindingFlags)
            reader r |> should equal actualValues


    type TupleTester =
        static member TestConstructor(t : 'Tuple) =
            let fields = FSharpValue.GetTupleFields t

            let ctor = FSharpValue.PreComputeTupleConstructorFast typeof<'Tuple>
            let result = ctor fields 
            Assert.IsInstanceOf<'Tuple> result
            result :?> 'Tuple |> should equal t

        static member TestReader(t : 'Tuple) =
            let actualValues = FSharpValue.GetTupleFields t

            let reader = FSharpValue.PreComputeTupleReaderFast typeof<'Tuple>
            reader t |> should equal actualValues


    type ExceptionTester =
        static member TestConstructor(e : 'Exception, ?bindingFlags) =
            let fields = FSharpValue.GetExceptionFields(e, ?bindingFlags = bindingFlags)

            let ctor = FSharpValue.PreComputeExceptionConstructorFast(e.GetType(), ?bindingFlags = bindingFlags)
            let result = ctor fields 
            Assert.IsInstanceOf<'Exception> result
            result :?> 'Exception |> should equal e

        static member TestReader(e : 'Exception, ?bindingFlags) =
            let actualValues = FSharpValue.GetExceptionFields(e, ?bindingFlags = bindingFlags)

            let reader = FSharpValue.PreComputeExceptionReaderFast(e.GetType(), ?bindingFlags = bindingFlags)
            reader e |> should equal actualValues

    //
    //  test cases
    //

    // Records

    type SimpleRecord =
            { Sr : string
              Ir : int
              Fr : float
              Or : obj } //object is somewhat special cased the constructor code

    type MutableRecord =
        { mutable Sm : string
          mutable Im : int
          mutable Fm : float }

    type internal InternalRecord = internal { Si : string }

    type private PrivateRecord = private { Fp : float }
    with static member Instance = { Fp = 3.14 }

    type GenericRecord<'a> = { Generic : 'a }

    [<Test>]
    let ``Record : Simple Construction``() =
        RecordTester.TestConstructor { Sr = "string" ; Ir = 12 ; Fr = 15.12 ; Or = new obj () }

    [<Test>]
    let ``Record : Simple Read``() =
        RecordTester.TestReader { Sr = "string" ; Ir = 12 ; Fr = 15.12 ; Or = new obj () }

    [<Test>]
    let ``Record : Mutable Construction``() =
        RecordTester.TestConstructor { Sm = "string" ; Im = 12 ; Fm = 15.12 }

    [<Test>]
    let ``Record : Mutable Read``() =
        RecordTester.TestReader { Sm = "string" ; Im = 12 ; Fm = 15.12 }

    [<Test>]
    let ``Record : Internal Construction``() =
        RecordTester.TestConstructor ({ Si = "string" }, BindingFlags.NonPublic)

    [<Test>]
    let ``Record : Internal Read``() =
        RecordTester.TestReader ({ Si = "string" }, BindingFlags.NonPublic)

    [<Test>]
    let ``Record : Private Construction``() =
        RecordTester.TestConstructor (PrivateRecord.Instance, BindingFlags.NonPublic)

    [<Test>]
    let ``Record : Private Read``() =
        RecordTester.TestReader (PrivateRecord.Instance, BindingFlags.NonPublic)

    [<Test>]
    let ``Record : Generic Construction``() =
        RecordTester.TestConstructor { Generic = 42 }

    [<Test>]
    let ``Record : Generic Read``() =
        RecordTester.TestReader { Generic = 42 }



    // Unions

    type SimpleUnion =
        | Empty
        | Su of string
        | Iu of int * string

    type SingletonUnion = Singleton

    type internal InternalUnion = internal | Si of string

    type internal PrivateUnion = private | Fp of float
    with static member Instance = Fp 3.14

    type GenericUnion<'a> = Generic of 'a | Other of Type

    type LargeUnion = A | B | C | E | F | H | I | J | K | L | M

    [<Test>]
    let ``Union : Option Construction`` () =
        UnionTester.TestConstructor (None : int option)
        UnionTester.TestConstructor (Some "hello")

    [<Test>]
    let ``Union : Option Read`` () =
        UnionTester.TestReader (None : int option)
        UnionTester.TestReader (Some "hello")

    [<Test>]
    let ``Union : List Construction`` () =
        UnionTester.TestConstructor ([] : int list)
        UnionTester.TestConstructor [1 .. 100]

    [<Test>]
    let ``Union : List Read`` () =
        UnionTester.TestReader ([] : int list)
        UnionTester.TestReader [1 .. 100]

    [<Test>]
    let ``Union : Simple Construction`` () =
        UnionTester.TestConstructor Empty
        UnionTester.TestConstructor (Su "string")
        UnionTester.TestConstructor (Iu (42, "string"))

    [<Test>]
    let ``Union : Simple Read`` () =
        UnionTester.TestReader Empty
        UnionTester.TestReader (Su "string")
        UnionTester.TestReader (Iu (42, "string"))

    [<Test>]
    let ``Union : Singleton Construction`` () =
        UnionTester.TestConstructor Singleton

    [<Test>]
    let ``Union : Singleton Read`` () =
        UnionTester.TestReader Singleton


    [<Test>]
    let ``Union : Internal Construction`` () =
        UnionTester.TestConstructor (Si "string", BindingFlags.NonPublic)


    [<Test>]
    let ``Union : Internal Read`` () =
        UnionTester.TestReader (Si "string", BindingFlags.NonPublic)

    [<Test>]
    let ``Union : Private Construction`` () =
        UnionTester.TestConstructor (Fp 3.14, BindingFlags.NonPublic)

    [<Test>]
    let ``Union : Private Read`` () =
        UnionTester.TestReader (Fp 3.14, BindingFlags.NonPublic)

    [<Test>]
    let ``Union : Generic Construction`` () =
        UnionTester.TestConstructor (Generic (2,"string"))

    [<Test>]
    let ``Union : Generic Read`` () =
        UnionTester.TestReader (Generic 12)


    [<Test>]
    let ``Union : Simple Tag Read`` () =
        UnionTester.TestTagReader <| Empty
        UnionTester.TestTagReader <| Su "string"
        UnionTester.TestTagReader <| Iu (42, "string")


    [<Test>]
    let ``Union : Internal Tag Read`` () =
        UnionTester.TestTagReader (Si "string", BindingFlags.NonPublic)

    [<Test>]
    let ``Union : Private Tag Read`` () =
        UnionTester.TestTagReader (Fp 3.14, BindingFlags.NonPublic)

    [<Test>]
    let ``Union : Generic Tag Read`` () =
        UnionTester.TestTagReader (Generic (1,2,3,4, null))

    [<Test>]
    let ``Union : Large Tag Read`` () =
        UnionTester.TestTagReader A
        UnionTester.TestTagReader C
        UnionTester.TestTagReader H
        UnionTester.TestTagReader M


    // exceptions

    exception SimpleExn of string * obj

    exception SingletonExn

    exception private PrivateExn of string * int

    [<Test>]
    let ``Exception : Simple Construction`` () =
        ExceptionTester.TestConstructor <| SimpleExn ("string", 42)

    [<Test>]
    let ``Exception : Simple Read`` () =
        ExceptionTester.TestReader <| SimpleExn ("string", 42)

    [<Test>]
    let ``Exception : Singleton Construction`` () =
        ExceptionTester.TestConstructor <| SingletonExn

    [<Test>]
    let ``Exception : Singleton Read`` () =
        ExceptionTester.TestReader <| SingletonExn

    [<Test>]
    let ``Exception : Private Construction`` () =
        ExceptionTester.TestConstructor (PrivateExn ("string", 42), BindingFlags.NonPublic)

    [<Test>]
    let ``Exception : Private Read`` () =
        ExceptionTester.TestReader (PrivateExn ("string", 42), BindingFlags.NonPublic)


    // Tuples

    [<Test>]
    let ``Tuple : Unary Construction`` () =
        TupleTester.TestConstructor <| Tuple<_>(42)

    [<Test>]
    let ``Tuple : Unary Read`` () =
        TupleTester.TestReader <| Tuple<_>(42)
        

    [<Test>]
    let ``Tuple : Pair Construction`` () =
        TupleTester.TestConstructor (42, "string")

    [<Test>]
    let ``Tuple : Pair Read`` () =
        TupleTester.TestReader (42, "string")

    [<Test>]
    let ``Tuple : Large Construction`` () =
        TupleTester.TestConstructor (42,"",false,(10," "),1,2,3,4,5, null, 2,34.123, None, 3)

    [<Test>]
    let ``Tuple : Large Read`` () =
        TupleTester.TestReader (42,"",false,(10," "),1,2,3,4,5, null, 2,34.123, None, 3)



//make sure it is faster!
module ReflectionPerformanceTest =

    open NUnit.Framework
    open Microsoft.FSharp.Reflection
    open System.Reflection //for bindingflags
    open FSharpx.Reflection

    let [<Literal>] numRepeats = 500000
    let [<Literal>] expectedImprovementTestor = 1L //conservative

    type MyRecord =
        { S : string
          i : int
          f : float }

    let repeat f = 
        let stopwatch = new System.Diagnostics.Stopwatch()
        stopwatch.Start()
        for i in 1..numRepeats do f i |> ignore
        stopwatch.Stop()
        stopwatch.ElapsedTicks

    let fastRecordCtor = FSharpValue.PreComputeRecordConstructorFast typeof<MyRecord>
    let standardRecordCtor = FSharpValue.PreComputeRecordConstructor typeof<MyRecord>

    let fastRecordReader = FSharpValue.PreComputeRecordReaderFast typeof<MyRecord>
    let standardRecordReader = FSharpValue.PreComputeRecordReader typeof<MyRecord>

    [<Test>]
    let ``should construct record faster than F# reflection``() =
        let fast = repeat (fun i -> fastRecordCtor [| "2"; i; 3. |] :?> MyRecord)
        let standard = repeat (fun i -> standardRecordCtor [| "2"; i; 3. |] :?> MyRecord)
        printf "FSharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)

    [<Test>]
    let ``should read record faster than F# reflection``() =
        let fast = repeat (fun i -> fastRecordReader { S = "2"; i = i; f = 3.0 })
        let standard = repeat (fun i -> standardRecordReader { S = "2"; i = i; f = 3.0 })
        printf "FSharpx is %ix faster" (standard/fast)       
        Assert.True(fast < standard/expectedImprovementTestor)

    type MyUnion =
        | Empty
        | One of int
        | Two of string * int

    let unionCases = FSharpType.GetUnionCases typeof<MyUnion>

    let fastUnionCtor = FSharpValue.PreComputeUnionCaseConstructorFast unionCases.[2]
    let standardUnionCtor = FSharpValue.PreComputeUnionConstructor unionCases.[2]

    let fastUnionReader = FSharpValue.PreComputeUnionCaseReaderFast unionCases.[2]
    let standardUnionReader = FSharpValue.PreComputeUnionReader unionCases.[2]

    let standardTagReader = FSharpValue.PreComputeUnionTagReader typeof<MyUnion>
    let fastTagReader = FSharpValue.PreComputeUnionTagReaderFast typeof<MyUnion>

    [<Test>]
    let ``should construct 2-case union faster than F# reflection``() =
        let fast = repeat (fun i -> fastUnionCtor [| "3"; i |] :?> MyUnion)
        let standard = repeat (fun i -> standardUnionCtor [| "3"; i |] :?> MyUnion)
        printfn "Fsharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)

    [<Test>]
    let ``should read 2-case union faster than F# reflection``() =
        let fast = repeat (fun i -> fastUnionReader (Two ("s",i)))
        let standard = repeat (fun i -> standardUnionReader (Two ("s",i)))
        printfn "FSharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)

    [<Test>]
    let ``should read union tags faster than F# reflection`` () =
        let fast = repeat (fun i -> fastTagReader (Two ("s",i)))
        let standard = repeat (fun i -> standardTagReader (Two ("s",i)))
        printfn "FSharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)


    let standardTupleCtor = FSharpValue.PreComputeTupleConstructor typeof<int * int * string>
    let fastTupleCtor = FSharpValue.PreComputeTupleConstructorFast typeof<int * int * string>
    
    let standardTupleReader = FSharpValue.PreComputeTupleReader typeof<int * int * string>
    let fastTupleReader = FSharpValue.PreComputeTupleReaderFast typeof<int * int * string>

    [<Test>]
    let ``should construct tuples faster than F# reflection`` () =
        let fast = repeat (fun i -> fastTupleCtor [|i ; i ; "s"|])
        let standard = repeat (fun i -> standardTupleCtor [|i ; i ; "s"|])
        printfn "FSharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)

    [<Test>]
    let ``should read tuples faster than F# reflection`` () =
        let fast = repeat (fun i -> fastTupleReader (i,i,"s"))
        let standard = repeat (fun i -> standardTupleReader (i,i,"s"))
        printfn "FSharpx is %ix faster" (standard/fast)
        Assert.True(fast < standard/expectedImprovementTestor)