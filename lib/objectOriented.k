/**
    This file is responsible for features about object-oriented programming.
**/

module OBJECTORIENTED-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports SPECIFICATION-SYNTAX
    imports AUXILIARY-SYNTAX
    imports FUNCTION-SYNTAX

/** 
    These are reserved variable names for object-oriented features. 
    Each object can obtain its class name, memory address, and function table 
    through these variable names.
        @ a._CLASS_
        @ b._ADDRESS_
        @ obj._FUNCTIONS_
    
    `equals` behaves just the same like it behaves in Java
 */
syntax Id ::= "_CLASS_"                     [token]
                | "_ADDRESS_"               [token]
                | "_FUNCTIONS_"             [token]

/**
    When attempting to search for a function within an object fails, 
    notify the program to continue searching in the global scope.
    Params:
        - Id: The function name
        - Types: The types of the function arguments
 */
syntax Function ::= continueSearchGlobalFunction(Id,Types)
/**
    Successfully found a function with matching arguments, and notify 
    the program to update the actual type (class) of the current object 
    when calling this function.
    Params:
        - Function: The target function to be called (already matched succesfully)
        - Id: The name of the class to which the member function actually belongs
 */
                | useFatherClassMemberFunction(Function,Id)

/**
    Create an object with given class, and set its all members (variables) to default values
        @ Member functions will be added to the object in this phase
    Params:
        - Id: The class name
 */
syntax KItem ::= create(Id)
/**
    Initialize the member function map for this class, and add the default no-argument 
    constructor (which can be overridden by user-defined constructors through the 
    polymorphism mechanism).
    Params:
        - Id: The class name
 */
                | initFunctionsMap(Id)
/**
    The members of the current class have been constructed, push it into `<memberStack>`, 
    and construct the members of its subclasses.
 */
                | addEnvLayer()
/**
    Store the member list of this object in the pre-allocated space.
 */
                | storeObject()
/**
    Search for a specific member variable in the given member list
    Params:
        - Id: The starting class name for the search 
            @ We adopt a mechanism similar to Java, where when accessing member variables, 
            the search goes upward (towards the parent class) based on the declared type 
            of the object, effectively hiding members from subclasses of the declared type).
        - Bool: Whether to start match variable name
            @ `true` for starting matching variable names
            @ `false` for continuing filtering the member list (hiding members from subclasses)
        - List: The member list of this object
        - Id: The variable name to be searched for
 */
                | lookupMemberVariable(Id,Bool,List,Id)

/**
    Search for the address of a specific member variable in the given member list
    Params:
        - Id: The starting class name for the search 
            @ We adopt a mechanism similar to Java, where when accessing member variables, 
            the search goes upward (towards the parent class) based on the declared type 
            of the object, effectively hiding members from subclasses of the declared type).
        - Bool: Whether to start match variable name
            @ `true` for starting matching variable names
            @ `false` for continuing filtering the member list (hiding members from subclasses)
        - List: The member list of this object
        - Id: The variable name to be searched for
    Returns:
        - The address of given member variable
 */
syntax Address ::= lookupMemberAddress(Id,Bool,List,Id)         [function]

/**
    Search for the closest member function with the highest parameter matching degree
    Params:
        - Id: The starting class name for the search 
            @ We adopt a mechanism similar to Java, where when accessing member functions, 
            the search goes upward (towards the parent class) based on the actual type 
            of the object, effectively hiding members from subclasses of the actual type).
        - Bool: Whether to start match function
            @ `true` for starting matching function
            @ `false` for continuing filtering the member list (hiding members from subclasses)
        - List: The member list of this object
        - Id: The function name to be searched for
        - Types: The types of arguments
        - Bool: Whether to continue searching for the function in the global scope 
            when no member function matches
            @ `true` means global search is allowed
            @ `false` means global search is not allowed
            @ It will be set to `true` ONLY when the member access operator (dot) is not used
        - Map: The inheritance relationships of all classes
            @ This parameter is used to pass to other auxiliary functions
    Returns:
        - The search result
            @ `useFatherClassMemberFunction()` style result means the search successfully ended
            @ `continueSearchGlobalFunction()` style result means no functions in the
            object match given arguments, waiting to further search in global functions
 */
syntax Function ::= lookupMemberFunction(Id,Bool,List,Id,Types,Bool,Map)     [function]

/**
    Obtain the member variables of the object in the style of subclass overriding parent class
    Params:
        - Id: The starting class name for the search
        - Bool: Whether to start match function
        - List: The member list of this object
        - Map: Used to store the return result
    Returns:
        - All member variables of this object (given class and its parent classes)
            @ Note: The return type is `Map`, not `List`, because variables with the same name 
            in a subclass override those with the same name in the parent class. 
            @ This method is only used for local variable overriding with the same name 
            before function calls.
 */
syntax Map ::= getMemberVariables(Id,Bool,List,Map)             [function]

endmodule

module OBJECTORIENTED
    imports OBJECTORIENTED-SYNTAX
    imports DOMAINS
    imports CONFIGURATION

/** Object-Oriented Features Start Here **/

// Class declaration
/**
    Rule for declaring a class
        Adds the class information to the `<classes>` cell and updates the `<inheritanceMap>`
 */
rule class _ extends _ ({} => {;}) 
rule    <k> class Class1 extends Class2 { S } => .K ...</k>
        <classes> 
        ...
        (.Bag =>
            <classData>
                <className> Class1 </className>
                <baseClass> Class2 </baseClass>
                <declarations> S </declarations>
            </classData>)
        ...
        </classes>
        <inheritanceMap> 
                ... (.Map => Class1 |-> Class2) ... 
        </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Object Member Function Declaration
/**
    Rule for declaring a member function
        Adds the function to the `_FUNCTIONS_` map in the environment
        @ When `<isGlobal>` is `false`, it means all functions declared now are member functions
 */
rule    <k> T:Type F:Id(Ps:Parameters) : RId:Id Specs:Specifications FBody => .K ...</k>
        <isGlobal> false </isGlobal>
        <env>
                ... _FUNCTIONS_ |-> ( Funs:Map => Funs[F <- (getTypes(Ps) |-> 
                        function(F, T, Ps, FBody, getRequires(Specs, .Requires), 
                        getEnsures(Specs, .Ensures), RId))]
                        )
                ...
        </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires notBool F in_keys(Funs)

/**
    Rule for updating an existing member function
        Updates the function definition in the `_FUNCTIONS_` map for the given parameter types
 */
rule    <k> T:Type F:Id(Ps:Parameters) : RId:Id Specs:Specifications FBody => .K ...</k>
        <isGlobal> false </isGlobal>
        <env>
                ... _FUNCTIONS_ |-> ( Funs:Map => Funs[F <- 
                                updateMap(convertToMap(Funs[F]), getTypes(Ps) |-> 
                                function(F, T, Ps, FBody, getRequires(Specs, .Requires), 
                                getEnsures(Specs, .Ensures), RId))
                                ]
                        )
                ...
        </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// `new` Object
/**
    Rule for creating a new object
    Perform the following steps:
        - Pre-allocate memory space for the object to be created
        - Push the program context into the stack in the style of a function call 
            @ Since the constructed object is eventually returned using `return` statement, 
            the process of creating an object is also treated as a function call, maintaining 
            consistency in syntax style. 
        - Call `create()` to create an instance of the class 
            @ All member variables are assigned default values
            That is to say, for the `int` type, it will be assigned 0; for the `bool` type, 
            it will be assigned `false`; and for objects, they will be assigned 
            `undefined(Class)` (similar to `null`).
        - Call `storeObject()` to store the members of the object in the pre-allocated space
        - Call the constructor function that matches the user-provided arguments to initialize 
            the member values
        - Finally, return a reference to the object

        @ Here we adopt a mechanism similar to the `oop-klass` model in Java to implement 
        the object creation process. However, there are differences in memory operations: 
            @@ In Java, modifications to (non-reference type) member variables directly modify 
            the values in the pre-allocated memory space.
            @@ In our implementation, all variables exist in a reference style (including basic 
            types). Therefore, even member variables of basic types exist in a reference manner 
            rather than storing values directly (member functions store their complete content 
            directly).
        So when we pre-allocate space, we have already linked the object and its member storage 
        space. (see the element `object(Class, Class, address(L))` in `<estack>`) 
        This provides convenience for the subsequent calling of the constructor function.
 */
rule    <k> new Class:Id(Vs:Vals) ~> K
                => create(Class) ~> (storeObject() ~> ((Class(Vs)); return this;)) 
        </k>
        <env> Env => .Map </env>
        <control>
                <fstack> .List => 
                ListItem(fstackFrame(T, Env, K, function(Class, Class, 
                        .Parameters, ;, .Requires, .Ensures, _RESULT_), Vs, 
                        Lstack,CurrentObject)) 
                ...
                </fstack>
                <lstack> Lstack </lstack>
                <estack> 
                        .List => ListItem(object(Class, Class, address(L))) ... 
                </estack>
                <returnType> T => Class </returnType>
                <crntObj> CurrentObject
                        =>  
                        <crntClass> Object </crntClass>
                        <memberStack> ListItem(objectMember(Object, .Map, .Map)) </memberStack>
                        <location> L </location>
                </crntObj>
        </control>
        <nextAddress> L:Int => L +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [priority(2)]

// Object Assignment
/**
    Rule for assigning an object reference to another reference
        Updates the `<store>` with the new object reference
        @ Only the actual type and address of the assigned variable is modified, 
        while its declared type is preserved.
        @ Requires that the actual class of the new object is a subtype of the 
        declared type of the old value.
 */
rule    <k> X:Id = object(DeclaredClass:Id, ActualClass:Id, NewAddress) 
                => object(DeclaredClass, ActualClass, NewAddress) ... 
        </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
        ... 
                A |-> (OldValue => object(typeToId(getDeclaredType(OldValue)), 
                        ActualClass, NewAddress))
        ... 
        </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        <lock> Locks </lock>
        requires subtypeOf(ActualClass, getDeclaredType(OldValue), IMap)
                andBool hasWriteAccess(TID, address(A), Locks)
        [group(assignment)]

/**
    Rule for assigning an object reference to a memory location
        @ The constraint conditions are consistent with the previous rule
 */
rule    <k> *address(L) = object(DeclaredClass:Id, ActualClass:Id, NewAddress) 
                => object(DeclaredClass, ActualClass, NewAddress) ... </k>
        <store> 
        ... 
                L |-> (OldValue => object(typeToId(getDeclaredType(OldValue)), 
                        ActualClass, NewAddress))
        ... 
        </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        <lock> Locks </lock>
        requires subtypeOf(ActualClass, getDeclaredType(OldValue), IMap)
                andBool hasWriteAccess(TID, address(L), Locks)
        [group(assignment)]

/**
    Rule for adding a no-argument constructor to the objects of this class
 */
rule    <k> initFunctionsMap(Class:Id) => .K ... </k>
        <env> ... .Map => _FUNCTIONS_ |-> (
                Class |-> (getTypes(.Parameters) |-> 
                        function(Class, void, .Parameters, ;, 
                        .Requires, .Ensures, _RESULT_)
                )
        ) 
        ...
        </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires Class =/=K Object

/**
    Rule for adding `equals` function to `Object` class
 */
rule    <k> initFunctionsMap(Object) => .K ... </k>
        <env> ... .Map => _FUNCTIONS_ |-> (
                Object |-> (getTypes(.Parameters) |-> 
                    function(Object, void, .Parameters, ;, 
                    .Requires, .Ensures, _RESULT_)
                )
                String2Id("equals") |-> (getTypes(Object String2Id("o")) |-> 
                    function(String2Id("equals"), bool, Object String2Id("o"), {
                        if(isUndefined(String2Id("o")))
                        {
                            return false;
                        }
                        return this._ADDRESS_ == String2Id("o")._ADDRESS_;
                    }, 
                    .Requires, .Ensures, _RESULT_)
                )
                String2Id("toString") |-> (getTypes(.Parameters) |-> 
                    function(String2Id("toString"), string, .Parameters, {
                        return "object(" + this.String2Id("_CLASS_") + "," 
                        + "address(" + this.String2Id("_ADDRESS_") + "))" ;
                    }, 
                    .Requires, .Ensures, _RESULT_)
                )
        ) 
        ...
        </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for creating an object of the given class
    Perform the following steps:
        - Create an instance of the parent class in this address space `L`
        - Set `<crntCLass>` to current class
        - Initialize the `_ADDRESS_` and `_CLASS_` variables
        - Initialize the function map for current class (add a no-argument constructor)
        - Declare members of this class
        - Adds a new environment layer for subclass to declare its members
 */
rule    <k> create(Class:Id)
            => create(FatherClass) ~> setCrntClass(Class) 
                ~> int _ADDRESS_ = L ; string _CLASS_ = Id2String(Class) ;
                ~> initFunctionsMap(Class)
                ~> S ~> addEnvLayer()
            ...
        </k>
        <crntObj>
            <location> L:Int </location>
            ...
        </crntObj>
        <className> Class </className>
        <baseClass> FatherClass:Id </baseClass>
        <declarations> S </declarations>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Special handling for the instantiation process of the `Object` class, 
    as it has no parent class.
 */
rule    <k> create(Object) 
                => setCrntClass(Object) 
                ~> int _ADDRESS_ = L ; string _CLASS_ = "Object" ;
                ~> initFunctionsMap(Object)
                ~> addEnvLayer() ...
        </k>
        <crntObj>
                        <location> L:Int </location>
                        ...
        </crntObj>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for adding a new environment layer for subclass
        Pushes the current environment and function map in `<env>` into the `<memberStack>`, 
        and clear `<env>`.
 */
rule    <k> addEnvLayer() => .K ...</k>
        <env> Env:Map _FUNCTIONS_ |-> Funs => .Map </env>
        <crntClass> Class:Id </crntClass>
        <memberStack> 
                .List => ListItem(objectMember(Class, Env, Funs)) ... 
        </memberStack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for saving the members of the object to the pre-allocated space
        @ The rightmost `objectMember(Object, .Map, .Map)` is ignored as an ending marker
        @ Note: Due to the style of our implementation mechanism, the member variables 
        are still default values at this point and have not been initialized with the 
        values provided by the user.
 */
rule    <k> storeObject() => .K ...</k>
        <crntObj>
                <memberStack> 
                        EStack ListItem(objectMember(Object, .Map, .Map)) => EStack
                </memberStack>
                (<location> L:Int </location> => .Bag)
                ...
        </crntObj>
        <store>... .Map => L |-> EStack ...</store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for `this` expression
        Directly look at the top element of the `<estack>` and return it
        @ Note: When using `this`, the declared type and the actual type of the returned object reference 
        are both the actual type of the current object.
 */
rule    <k> this => object(AClass, AClass, A) ... </k>
        <estack> ListItem(object(_:Id, AClass:Id, A:Address)) _ </estack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for `super` expression
        Return an object reference whose declared type and actual type are both the direct parent class 
        of the current object's actual type, and have the same address as the current object.
 */
rule    <k> super => object(FatherClass, FatherClass, A) ... </k>
        <estack> ListItem(object(_:Id, AClass:Id, A:Address)) _ </estack>
        <classData>
                <className> AClass </className>
                <baseClass> FatherClass </baseClass>
                ...
        </classData>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Force type cast
// When explicitly casting, only modify the declared type, not the actual type
rule (C:Id) object(_:Id, AClass:Id, A:Address) => object(C, AClass, A)          [anywhere]

/**
    Rule for calling the parent class constructor
        @ Note: When calling a member function, the search is based on the actual type of the current object.
 */
rule    <k> super(Vs:Vals) => FatherClass(Vs) ... </k>
        <estack> ListItem(object(_:Id, AClass:Id, _)) _ </estack>
        <classData>
                <className> AClass </className>
                <baseClass> FatherClass </baseClass>
                ...
        </classData>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for getting the actual type of an object
 */
rule typeOf(object(_:Id, AClass:Id, _:Address)) => AClass

// Member variable access
/**
    Rule for accessing a member variable of the current object
 */
rule    <k> object(DClass, _:Id, address(L):Address). X:Id
                => lookupMemberVariable(DClass, false, MemberList, X) ...
        </k>
        <store> ... L |-> MemberList ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Helper rules for `lookupMemberVariable`
 */
rule lookupMemberVariable(WantedClass:Id, false, 
        ListItem(objectMember(WantedClass, Vars, Funs)) L, X:Id)
        => lookupMemberVariable(WantedClass, true, 
                ListItem(objectMember(WantedClass, Vars, Funs)) L, X)

rule lookupMemberVariable(WantedClass:Id, false, 
        ListItem(objectMember(ThisClass, _, _)) L, X:Id)
        => lookupMemberVariable(WantedClass, false, L, X)
        requires WantedClass =/=K ThisClass

// found in current class layer
rule    <k> lookupMemberVariable(_, true, ListItem(
                objectMember(_, X |-> address(L) _, _)) _, X) 
                => V ...
        </k>
        <store> ... L |-> V ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <lock> Locks </lock>
        requires hasWriteAccess(TID, address(L), Locks)

// not found in current class layer
rule lookupMemberVariable(Class, true, ListItem(objectMember(_, Vars, _)) L, X)
        => lookupMemberVariable(Class, true, L, X)
        requires notBool(X in keys(Vars))

// Member function access
/**
    Rule for accessing a member function of the current object
        Push the new function caller information (current object) into `<estack>`,
        then use the helper function `lookupMemberFunction()` to perform the search.
        @ Note: Here, the caller is explicitly specified as an instance object, so if the match fails, 
        it cannot continue to match in the global functions.
 */
context HOLE::Exp . _Id (_::Exps)
rule    <k> object(DClass:Id, AClass:Id, address(L):Address) . F:Id (Vs:Vals) 
                => lookupMemberFunction(AClass, false, MemberList, F, 
                        getTypes(Vs), false, IMap) (Vs)
                ... 
        </k>
        <estack> .List => ListItem(object(DClass, AClass, address(L))) ... </estack>
        <store> ... L |-> MemberList:List ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for accessing a member function of the current object
        When directly using the function name to call a function, and the program is currently 
        in an instance object, first write the call information into `<estack>` with the current 
        object as the caller, and search for an executable function. 
        If the search fails, then allow the search to continue in the global functions, and the 
        modification of the caller is completed when the search is switched to the global.
 */
rule    <k> (F:Id => lookupMemberFunction(AClass, false, MemberList, F, 
                        getTypes(Vs), true, IMap)) (Vs:Vals) 
                ... 
        </k>
        <estack> ListItem(object(DClass, AClass, address(L))) SL 
                => ListItem(object(AClass, AClass, address(L))) 
                        ListItem(object(DClass, AClass, address(L))) SL
        </estack>
        <store> ... L |-> MemberList:List ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Helper rules for looking up a member function in the member list
        The search strategy of this function is completely consistent with `lookupMemberVariable()`, 
        and the reader should be able to understand it quickly.
 */
rule lookupMemberFunction(WantedClass:Id, false, 
        ListItem(objectMember(WantedClass, Vars, Funs)) L, X:Id, Ts, B, IMap)
        => lookupMemberFunction(WantedClass, true, 
                ListItem(objectMember(WantedClass, Vars, Funs)) L, X, Ts, B, IMap)

rule lookupMemberFunction(WantedClass:Id, false,
        ListItem(objectMember(ThisClass, _, _)) L, X:Id, Ts, B, IMap)
        => lookupMemberFunction(WantedClass, false, L, X, Ts, B, IMap)
        requires WantedClass =/=K ThisClass

/**
    Here, the implementation mechanism is slightly different from that of lookupMemberVariable: 
        @ when searching for member variables, we only need to return the first matching result. 
            @@ Under the inheritance mechanism, the same-named variables of the subclass should override 
            those of the parent class. This overriding is mandatory when the same-named variable is not 
            explicitly specified to use the parent class's same-named variable (e.g., a.super.x), and it 
            is not automatically switched due to type matching problems. 
            @@ When searching for member functions, since we have implemented the overriding and overloading 
            mechanisms in polymorphism, the same-named functions may be scattered in multiple parent and child 
            classes. Therefore, when there is no matching function in the current class, we should continue 
            to search in the parent class.
        So here, we first check if there is a matching function in the current class (through `hasSuperTypeInList()`), 
        and if so, we match the one with the smallest parameter distance (by calculating `findCloestSuperType()`). 
        Otherwise, we should discard this layer and continue to try to match in the parent class.
 */
rule lookupMemberFunction(_, true, 
        ListItem(objectMember(Class:Id, _, F |-> FTable:Map _)) _, F, Ts, _, IMap) 
        => useFatherClassMemberFunction(matchFunction(findCloestSuperType(
                Ts, keys_list(FTable), IMap, 99999, .Types), FTable), Class)
        requires hasSuperTypeInList(Ts, keys_list(FTable), IMap)

// not found in current class layer
rule lookupMemberFunction(Class, true, 
        ListItem(objectMember(_, _, Funs)) L, F, Ts, B, IMap)
        => lookupMemberFunction(Class, true, L, F, Ts, B, IMap)
        requires notBool (F in keys(Funs))

// there are functions with the name, but all of their parameter lists are not compatible
rule lookupMemberFunction(Class, true, 
        ListItem(objectMember(_, _, F |-> FTable:Map _)) L, F, Ts, B, IMap)
        => lookupMemberFunction(Class, true, L, F, Ts, B, IMap)
        requires notBool hasSuperTypeInList(Ts, keys_list(FTable), IMap)

// not founded in current object, and allowed to search in global functions
rule lookupMemberFunction(_, true, .List, F, Ts, true, _)
        => continueSearchGlobalFunction(F, Ts)

/**
    Set the actual type of the member function caller to the current successfully matched class
 */
rule    <k> useFatherClassMemberFunction(V:Function, Class:Id) (Es) => V (Es) ... </k>
        <estack> ListItem(object(_, _ => Class, _)) ... </estack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    After the member function search fails, continue to search in global functions
    Change the function caller from the pre-set object reference to .Map (indicating that it is a global function call)
 */
rule    <k> continueSearchGlobalFunction(F:Id, Ts:Types) 
                => matchFunction(findCloestSuperType(
                Ts, keys_list(Funs), IMap, 99999, .Types), Funs) ... 
        </k>
        <estack> ListItem((_:ObjectReference => .Map)) ... </estack>
        <gFunctions> ... F |-> Funs:Map ... </gFunctions>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Get Address
/**
    Rule for getting the address of a member variable of the current object
        We just simply convert it to the helper function `lookupMemberAddress`
        @ Note: When accessing member variables, the declared type should be used 
        as the starting point for the search.
 */
context & HOLE::Exp . _:Id
rule    <k> & object(DClass:Id, _, address(L):Address). X:Id 
                => lookupMemberAddress(DClass, false, MemberList, X) ... 
        </k>
        <store> ... L |-> MemberList ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Helper rules for looking up the address of a member variable in the member list
        The search strategy of this function is completely the same as `lookupMemberVariable()`
 */
rule lookupMemberAddress(WantedClass:Id, false, 
        ListItem(objectMember(WantedClass, Vars, Funs)) L, X:Id)
        => lookupMemberAddress(WantedClass, true, 
                ListItem(objectMember(WantedClass, Vars, Funs)) L, X)

rule lookupMemberAddress(WantedClass:Id, false, 
        ListItem(objectMember(ThisClass, _, _)) L, X:Id)
        => lookupMemberAddress(WantedClass, false, L, X)
        requires WantedClass =/=K ThisClass

// found        
rule lookupMemberAddress(_, true, ListItem(objectMember(_, X |-> A _, _)) _, X) 
        => A 

// not found in current class layer
rule lookupMemberAddress(WantedClass, true, 
        ListItem(objectMember(_, Vars, _)) L, X)
        => lookupMemberAddress(WantedClass, true, L, X)
        requires notBool(X in keys(Vars))

// Member variable assignment
/**
    Rule for assigning a value to a member variable
        For the assignment of member variables, we uniformly convert it to the operation of 
        writing to the address space corresponding to the member variable.
 */
context HOLE::Exp . _:Id = _
rule    <k> object(DClass:Id, _, address(L):Address). X:Id = V:Val 
                => lookupMemberAddress(DClass, false, MemberList, X) = V
                ... 
        </k>
        <store> ... L |-> MemberList ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [group(assignment)]

/**
    Helper rules to add the member variables of the current object to `<env>`
        Determine whether the current execution is within an instance object based on 
        the value at the top of `<estack>`
 */
// not in any object, no members added
rule    <k> addObjectMembers() => .K ... </k>
        <estack> ListItem(_:Map) ... </estack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// add current object members to `env`
rule    <k> addObjectMembers() => .K ... </k>
        <estack> ListItem(object(_, AClass:Id, address(L:Int))) ... </estack>
        <env> Env 
                => updateMap(Env, getMemberVariables(AClass, false, MemberList, .Map)) 
        </env>
        <store> ... L |-> MemberList ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Helper rules for getting all the member variables
            @ Note: Object memberList (the third argument) represents subclasses and parent classes from 
            left to right. Therefore, when filtering subclasses, filter from the left side; when collecting 
            variables and overriding, start from the right side, so that the parent class variables will 
            be collected first and then can be overridden by the later results.
 */
rule getMemberVariables(_, _, .List, M) => M
rule getMemberVariables(StartClass, false, 
        ListItem(objectMember(CurrentClass:Id, _:Map, _:Map)) L:List, M)
        => getMemberVariables(StartClass, false, L, M)
        requires StartClass =/=K CurrentClass
rule getMemberVariables(StartClass, false, 
        ListItem(objectMember(CurrentClass:Id, ThisLayer:Map, Funs:Map)) L:List, M)
        => getMemberVariables(StartClass, true, 
                ListItem(objectMember(CurrentClass, ThisLayer, Funs)) L, M)
        requires StartClass ==K CurrentClass
rule getMemberVariables(StartClass, true, 
        L:List ListItem(objectMember(_:Id, ThisLayer:Map, _)), M:Map)
        => getMemberVariables(StartClass, true, L, updateMap(M, ThisLayer))

/**
    Rule for `instanceOf` expression
        Use the helper function `subtypeOf()` to determine if the actual type of the object is a subclass of `C`
 */
rule    <k> object(_:Id, AClass:Id, _:Address) instanceOf C:Id
                => subtypeOf(AClass, C, IMap) ...
        </k>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rules for `invoke` expression (reflection)
        These rules should be straightforward
 */
rule invoke(Es:Exps) => runtimeError("`invoke()` arguments less than 2")        
        requires lengthOf(Es) <Int 2

rule invoke(Obj:ObjectReference, FunctionName:String, Arguments:Exps)
        => Obj.(String2Id(FunctionName)) (Arguments)

/** Object-Oriented Features End Here **/

endmodule