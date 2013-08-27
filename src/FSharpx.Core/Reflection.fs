namespace FSharpx

module internal ReflectImpl =

    open System
    open System.Reflection
    open System.Linq.Expressions

    open Microsoft.FSharp.Quotations
    open Microsoft.FSharp.Linq.RuntimeHelpers
    open Microsoft.FSharp.Reflection


    let inline isPrivateRepresentation (t : Type) =
        let msg = sprintf "The type '%s' has private representation. You must specify BindingFlags.NonPublic to access private type representations." t.Name
        invalidArg "bindingFlags" msg

    // LINQ Expression utils
    module Expression =

        let inline compile1<'U, 'V>(f : Expression -> Expression) =
            let parameter = Expression.Parameter(typeof<'U>)
            let lambda = Expression.Lambda<Func<'U,'V>>(f parameter, parameter)
            let f = lambda.Compile()
            f.Invoke

        let inline compile2<'U1, 'U2, 'V>(f : Expression -> Expression -> Expression) =
            let p1 = Expression.Parameter typeof<'U1>
            let p2 = Expression.Parameter typeof<'U2>
            let lambda = Expression.Lambda<Func<'U1,'U2,'V>>(f p1 p2, p1, p2)
            let f = lambda.Compile()
            f.Invoke

        let pair<'T, 'U>(e1 : Expression, e2 : Expression) =
            let ctor = typeof<System.Tuple<'T,'U>>.GetConstructor([| typeof<'T> ; typeof<'U> |])
            Expression.New(ctor , [| e1 ; e2 |])

        let throw<'exn when 'exn :> exn> (t : Type) (expr : Expr<'exn>) =
            let exnExpr = LeafExpressionConverter.QuotationToExpression expr
            Expression.Throw(exnExpr, t)

        let failwith<'exn, 'T when 'exn :> exn> (message : string) =
            let ctor = typeof<'exn>.GetConstructor [| typeof<string> |]
            let exn = Expression.New(ctor, Expression.Constant message)
            Expression.Throw(exn, typeof<'T>) 

        let unbox (t : Type) (e : Expression) =
            if t = typeof<obj> then e 
            else
                Expression.Convert(e, t) :> Expression

        let box (e : Expression) = Expression.TypeAs(e, typeof<obj>) :> Expression

        let unboxElement (objArray : Expression) (idx : int) (t : Type) =
            unbox t <| Expression.ArrayIndex(objArray, Expression.Constant idx)

        /// calls constructor with arguments boxed in object array
        let callConstructorBoxed (ctorInfo : ConstructorInfo) (objArray : Expression) =
            let unboxedParams = 
                ctorInfo.GetParameters() 
                |> Array.mapi (fun i p -> unboxElement objArray i p.ParameterType)
            Expression.New(ctorInfo, unboxedParams)

        /// calls method with arguments boxed in object array
        let callMethodBoxed (methodInfo : MethodInfo) (instance : Expression option) (objArray : Expression) =
            let unboxedParams =
                methodInfo.GetParameters() 
                |> Array.mapi (fun i p -> unboxElement objArray i p.ParameterType)

            match instance with
            | None when methodInfo.IsStatic -> Expression.Call(methodInfo, unboxedParams)
            | Some instance when not methodInfo.IsStatic -> Expression.Call(instance, methodInfo, unboxedParams)
            | None -> invalidArg methodInfo.Name "Expected static method."
            | Some _ -> invalidArg methodInfo.Name "Expected non-static method."

        /// calls collection of property getters on given instance expression
        /// and returns an array expression of boxed results
        let callPropertyGettersBoxed (declaringType : Type) (properties : PropertyInfo []) (instance : Expression) =
            assert(properties |> Array.forall (fun p -> p.DeclaringType = declaringType))

            let calls = properties |> Seq.map (fun p -> Expression.Property(instance, p) |> box)
            Expression.NewArrayInit(typeof<obj>, calls)

    //
    //  System.Tuple
    //

    let preComputeTupleReader (tupleType : Type) =
        let rec traverseTuple (tupleType : Type) (tupleExpr : Expression) =
            let fieldExprs = 
                tupleType.GetProperties()  
                |> Seq.filter (fun p -> p.Name.StartsWith("Item")) 
                |> Seq.sortBy (fun p -> p.Name)
                |> Seq.map (fun p -> Expression.Property(tupleExpr, p) |> Expression.box)

            let restExprs =
                match tupleType.GetProperty("Rest") with
                | null -> Seq.empty
                | rest ->
                    let restExpr = Expression.Property(tupleExpr, rest)
                    traverseTuple rest.PropertyType restExpr

            Seq.append fieldExprs restExprs

        if not <| FSharpType.IsTuple tupleType then
            invalidArg "tupleType" <| sprintf "Type '%s' is not a tuple type." tupleType.Name


        Expression.compile1<obj, obj []>(fun param ->
            let fieldExprs = traverseTuple tupleType (param |> Expression.unbox tupleType)
            Expression.NewArrayInit(typeof<obj>, fieldExprs) :> _)


    let preComputeTupleConstructor (tupleType : Type) =
        let rec composeTuple (objArray : Expression) (tupleType : Type) offset =
            let ctorInfo, nested = FSharpValue.PreComputeTupleConstructorInfo tupleType

            let unboxElem i (p : ParameterInfo) = 
                Expression.unboxElement objArray (i+offset) p.ParameterType

            match nested with
            | None ->
                let paramExprs = ctorInfo.GetParameters() |> Seq.mapi unboxElem
                Expression.New(ctorInfo, paramExprs)
            | Some restType ->
                let ctorParams = ctorInfo.GetParameters()
                let n = ctorParams.Length
                let fieldExprs = ctorParams |> Seq.take (n - 1) |> Seq.mapi unboxElem
                let restExprs = composeTuple objArray restType (offset + n - 1)
                Expression.New(ctorInfo, Seq.append fieldExprs [| restExprs |])

        if not <| FSharpType.IsTuple tupleType then
            invalidArg "tupleType" <| sprintf "Type '%s' is not a tuple type." tupleType.Name

        Expression.compile1<obj [], obj>(fun boxedParams -> 
            composeTuple boxedParams tupleType 0 |> Expression.box)

    //
    //  F# Discriminated Unions
    //

    let checkAccessibility (uci : UnionCaseInfo) bindingFlags =
        if not <| FSharpType.IsUnion(uci.DeclaringType, ?bindingFlags = bindingFlags) then
            isPrivateRepresentation uci.DeclaringType

    let callUnionTagReader (union : Type) bindingFlags (instance : Expression) =
        match FSharpValue.PreComputeUnionTagMemberInfo(union, ?bindingFlags = bindingFlags) with
        | null -> isPrivateRepresentation union
        | :? PropertyInfo as p -> Expression.Property(instance, p) :> Expression
        | :? MethodInfo as m when m.IsStatic -> Expression.Call(m, instance) :> Expression
        | :? MethodInfo as m -> Expression.Call(instance, m) :> Expression
        | _ -> invalidOp "unexpected error"

    let callUnionCaseReader (uci : UnionCaseInfo) (instance : Expression) =
        let fields = uci.GetFields()
        let branchType = if fields.Length = 0 then uci.DeclaringType else fields.[0].DeclaringType
        let unboxedInstance = Expression.unbox branchType instance
        Expression.callPropertyGettersBoxed branchType fields unboxedInstance :> Expression

    let callUnionCaseConstructor (uci : UnionCaseInfo) bindingFlags (boxedArgs : Expression) =
        let ctor = FSharpValue.PreComputeUnionConstructorInfo(uci, ?bindingFlags = bindingFlags)
        Expression.callMethodBoxed ctor None boxedArgs |> Expression.box

    let preComputeUnionTagReader (union : Type) bindingFlags =
        Expression.compile1<obj, int>(fun instance ->
            let unboxedInstance = Expression.unbox union instance
            callUnionTagReader union bindingFlags unboxedInstance)

    let preComputeUnionCaseReader (uci : UnionCaseInfo) bindingFlags =
        checkAccessibility uci bindingFlags
        Expression.compile1<obj, obj []>(callUnionCaseReader uci)

    let preComputeUnionCaseConstructor (uci : UnionCaseInfo) bindingFlags =
        checkAccessibility uci bindingFlags
        Expression.compile1<obj [], obj>(callUnionCaseConstructor uci bindingFlags)

    let preComputeUnionReader (union : Type) bindingFlags =
        let ucis = FSharpType.GetUnionCases(union, ?bindingFlags = bindingFlags)

        let defaultBody = 
            Expression.failwith<InvalidOperationException, UnionCaseInfo * obj []> "Invalid F# union tag."

        let getBranchCase (instance : Expression) (uci : UnionCaseInfo) =
            let values = callUnionCaseReader uci instance
            let uciExpr = Expression.Constant(uci, typeof<UnionCaseInfo>)
            let result = Expression.pair<UnionCaseInfo, obj []>(uciExpr, values)
            Expression.SwitchCase(result, Expression.Constant uci.Tag)

        Expression.compile1<obj, UnionCaseInfo * obj []>(fun boxedInstance ->
            let unboxedInstance = Expression.unbox union boxedInstance
            let tag = callUnionTagReader union bindingFlags unboxedInstance
            let cases = ucis |> Array.map (getBranchCase unboxedInstance)
            Expression.Switch(tag, defaultBody, cases) :> _)

    let preComputeUnionConstructor (union : Type) bindingFlags =
        let ucis = FSharpType.GetUnionCases(union, ?bindingFlags = bindingFlags)
        let defaultBody = Expression.failwith<ArgumentException, obj>("Supplied F# union tag is out of range.")
        let getBranchCtor (boxedArgs : Expression) (uci : UnionCaseInfo) =
            let result = callUnionCaseConstructor uci bindingFlags boxedArgs
            Expression.SwitchCase(result, Expression.Constant uci.Tag)

        Expression.compile2<int, obj [], obj>(fun tag args ->
            let branchCtors = ucis |> Array.map (getBranchCtor args)
            Expression.Switch(tag, defaultBody, branchCtors) :> _)


    //
    //  F# records
    //

    let preComputeRecordConstructor (record : Type) bindingFlags =
        let ctor = FSharpValue.PreComputeRecordConstructorInfo(record, ?bindingFlags = bindingFlags)

        Expression.compile1<obj [], obj>(fun e -> Expression.callConstructorBoxed ctor e |> Expression.box)

    let preComputeRecordReader (record : Type) bindingFlags =
        let fields = FSharpType.GetRecordFields(record, ?bindingFlags = bindingFlags)

        Expression.compile1<obj, obj []>(fun e -> 
            let ue = Expression.unbox record e
            Expression.callPropertyGettersBoxed record fields ue :> _)


    //
    //  F# exceptions
    //

    // an implementation that curiously does not exist in Microsoft.FSharp.Reflection
    let preComputeExceptionConstructorInfo (exceptionType : Type) bindingFlags : ConstructorInfo =
        let signature = 
            FSharpType.GetExceptionFields(exceptionType, ?bindingFlags = bindingFlags) 
            |> Array.map(fun f -> f.PropertyType)

        let ctors = 
            match bindingFlags with 
            | Some f -> exceptionType.GetConstructors (f ||| BindingFlags.Instance) 
            | None -> exceptionType.GetConstructors()

        let testCtor (ctor : ConstructorInfo) = 
            ctor.GetParameters() |> Array.map (fun p -> p.ParameterType) = signature

        match Array.tryFind testCtor ctors with
        | None -> isPrivateRepresentation exceptionType
        | Some ctorInfo -> ctorInfo


    let preComputeExceptionConstructor (exceptionType : Type) bindingFlags =
        let ctor = preComputeExceptionConstructorInfo exceptionType bindingFlags

        Expression.compile1<obj [], obj>(fun e -> Expression.callConstructorBoxed ctor e |> Expression.box)

    let preComputeExceptionReader (exceptionType : Type) bindingFlags =
        let fields = FSharpType.GetExceptionFields(exceptionType, ?bindingFlags = bindingFlags)

        Expression.compile1<obj, obj []>(fun e -> 
            let ue = Expression.unbox exceptionType e
            Expression.callPropertyGettersBoxed exceptionType fields ue :> _)


namespace FSharpx.Reflection

    open System
    open System.Reflection
    open Microsoft.FSharp.Reflection

    type FSharpValue =
        static member PreComputeRecordConstructorFast(recordType:Type,?bindingFlags:BindingFlags) =
            FSharpx.ReflectImpl.preComputeRecordConstructor recordType bindingFlags
        static member PreComputeUnionCaseConstructorFast(unionCase:UnionCaseInfo, ?bindingFlags:BindingFlags) =
            FSharpx.ReflectImpl.preComputeUnionCaseConstructor unionCase bindingFlags
        static member PreComputeUnionConstructorFast(unionType:Type,?bindingFlags:BindingFlags) =
            FSharpx.ReflectImpl.preComputeUnionConstructor unionType bindingFlags
        static member PreComputeTupleConstructorFast(tupleType:Type) =
            FSharpx.ReflectImpl.preComputeTupleConstructor tupleType
        static member PreComputeExceptionConstructorFast(exceptionType:Type,?bindingFlags) =
            FSharpx.ReflectImpl.preComputeExceptionConstructor exceptionType bindingFlags

        static member PreComputeRecordReaderFast(recordType:Type, ?bindingFlags:BindingFlags) : obj -> _ =
            FSharpx.ReflectImpl.preComputeRecordReader recordType bindingFlags
        static member PreComputeUnionCaseReaderFast(unionCase:UnionCaseInfo, ?bindingFlags:BindingFlags) : obj -> _ =
            FSharpx.ReflectImpl.preComputeUnionCaseReader unionCase bindingFlags
        static member PreComputeUnionReaderFast(unionType:Type, ?bindingFlags:BindingFlags) : obj -> _ =
            FSharpx.ReflectImpl.preComputeUnionReader unionType bindingFlags 
        static member PreComputeTupleReaderFast(tupleType:Type) : obj -> _ =
            FSharpx.ReflectImpl.preComputeTupleReader tupleType
        static member PreComputeExceptionReaderFast(exceptionType:Type,?bindingFlags) : obj -> _ =
            FSharpx.ReflectImpl.preComputeExceptionReader exceptionType bindingFlags

        static member PreComputeUnionTagReaderFast(unionType:Type,?bindingFlags) : obj -> _ =
            FSharpx.ReflectImpl.preComputeUnionTagReader unionType bindingFlags

        static member PreComputeExceptionConstructorInfo(exceptionType,?bindingFlags) : ConstructorInfo =
            FSharpx.ReflectImpl.preComputeExceptionConstructorInfo exceptionType bindingFlags