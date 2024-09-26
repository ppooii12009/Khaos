/**
    This file is responsible for handling function declarations and the calling process. 
    Note: Object-oriented style calls (i.e., member function calls) are not included in this file.
    The process is : 
        - Check if there is a function table corresponding to the function name in `<gFunctions>`
        - If so, try to match the function with the highest degree of parameter type matching
            (by calculating `typeDifference()`, then pick the one with minimal value)
        - If the function matching is successful, push the environment information into the `<fstack>`, 
            and reset `<env>` to `<gVariables>`
        - Import member variables of the current object (if any)
        - Declare parameters and bind them with the values of the arguments
        - Execute the function body
        - Return and restore the corresponding environment
 */

module FUNCTION-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports SPECIFICATION-SYNTAX
    imports AUXILIARY-SYNTAX

/**
    Syntax declaration for function
    Params:
        - Id: Function name
        - Type: Return value type
        - Parameters: Parameters
        - Stmt: Function body
        - Requires: Preconditions
        - Ensures: Postconditions
        - Id: Name of the returned value 
            @ Used for postconditions check
            @ If no explicit name is given, it defaults to "_RESULT_"
 */
syntax Function ::= function(Id,Type,Parameters,Stmt,Requires,Ensures,Id)
/**
    Params:
        - Types: Types of parameters
        - Map: Function table corresponding to the function name which is called
    Returns:
        - Function with parameter types that exactly match the given ones
 */
                | matchFunction(Types,Map)                          [function]
syntax Val ::= Function

/**
    Params:
        - Type: The return value type of the currently executing function
        - Map: `<env>` before function call
        - K: Program not completed before function call
        - Function: Definition of the function being called
        - Vals: Values of the arguments passed in
        - List: Value of `<lstack>` before function call
        - K: The object currently being constructed (unfinished)
 */
syntax KItem ::= fstackFrame(Type,Map,K,Function,Vals,List,K)


// Add the member variables of the current object to `<env>` 
// (used during function/method call)
syntax KItem ::= addObjectMembers()

endmodule

module FUNCTION
    imports FUNCTION-SYNTAX
    imports DOMAINS
    imports CONFIGURATION
    imports TYPE
    imports EXP
    imports STMT
    imports SPECIFICATION
    imports AUXILIARY

// Type of the function, is the same as the return value
rule typeOf(function(_:Id, T:Type, _:Parameters, _:Stmt, _:Requires, 
        _:Ensures, _:Id)) => T

rule matchFunction(Ts:Types, Ts |-> F:Function _:Map) => F      [anywhere]

// Global Function Declaration
/**
    Rule for declaring a global function (when `<isGlobal>` is true)
        Adds the function to the `<gFunctions>` map, mapping the parameter types
        to the function definition.
        @ Requires that the function name is not already present in `<gFunctions>`.
 */
rule    <k> T:Type F:Id(Ps:Parameters) : RId:Id Specs:Specifications FunctionBody 
            => .K ...
        </k>
        <isGlobal> true </isGlobal>
        <gFunctions> 
                GFun => GFun[F <- (getTypes(Ps) |-> 
                            function(F, T, Ps, FunctionBody, getRequires(Specs, .Requires), 
                                getEnsures(Specs, .Ensures), RId)
                            )
                        ]
        </gFunctions>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires notBool F in_keys(GFun)

/**
    Rule for updating an existing global function declaration
        Updates the function definition in the `<gFunctions>` map for the given
        parameter types.
 */
rule    <k> T:Type F:Id(Ps:Parameters) : RId:Id Specs:Specifications FunctionBody 
            => .K ...
        </k>
        <isGlobal> true </isGlobal>
        <gFunctions> 
        ... 
            F |-> (Funs:Map => updateMap(Funs, getTypes(Ps) |-> 
                        function(F, T, Ps, FunctionBody, getRequires(Specs, .Requires), 
                        getEnsures(Specs, .Ensures), RId)))
        ...
        </gFunctions>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Function call
/**
    Rule for calling a function
        When the top element of `<estack>` is a `Map`, it means the current context 
        is not within any object (i.e., in the global environment). 
        In this case, the called function is a global function. 
        We directly match the function with the closest argument types in `<gFunctions>`.
 */
rule    <k> (X:Id => 
                matchFunction(findCloestSuperType(
                        getTypes(Vs), keys_list(Funs), IMap, 99999, .Types), Funs
                        ))(Vs:Vals) 
                ... 
        </k>
        <estack> ListItem(M:Map) L => ListItem(.Map) ListItem(M) L </estack>
        <gFunctions>... X |-> Funs:Map ...</gFunctions>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [group(lookup)]

// Function application
/**
    Rule for applying a function
    Perform the following steps:
        - Set `<env>` to global variables `GVar`
        - Save the current environment context (including the object being constructed)
        - Add object members to the environment (if any)
        - Declare parameters and binds them to the provided values (arguments)
        - Check preconditions (if present and not skipped)
        - Execute the function body
        - Add a default `return` statement in case the user forgot it
 */
rule    <k> function(F,T,Ps,S,Rs,Es,RId)(Vs:Vals) ~> K 
                => 
                addObjectMembers() ~> mkDecls(Ps,Vs)
                ~> 
                #if (Rs =/=K .Requires andBool (notBool SkipCheck))
                #then
                        setSkipCheck(true) ~> setSkipPrint(true)
                        ~>
                        forcePrintln("precondition(s) of [ " + #toString(F)
                        + "(" + #toString(Vs) + ") ] check result : ");
                        forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                        ~> 
                        checkRequires(1, Rs)
                        ~>
                        forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                        ~> setSkipCheck(false) ~> setSkipPrint(false)
                #else
                        .K
                #fi
                ~>
                S
                return; 
        </k>
        <control>
                <fstack> 
                        .List => ListItem(fstackFrame(T',Env,K,
                        function(F,T,Ps,S,Rs,Es,RId),Vs,
                        Lstack,CrntObj)) ...
                </fstack>
                <lstack> Lstack </lstack>
                <estack> _ </estack>
                <returnType> T' => T </returnType>
                <crntObj> CrntObj </crntObj>
        </control>
        <env> Env => GVars </env>
        <skipCheck> SkipCheck </skipCheck>
        <gVariables> GVars </gVariables>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for handling a `return;` statement without a value
        Replace it with `return nothing(T);`, where `T` is the return type.
 */
rule    <k> return; => return nothing(T); ...</k> 
        <returnType> T </returnType>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for handling a `return` statement with a value
    Perform the following steps:
        - Check if the actual return value is compatible with the declared return type
            @ This is ensured by the `requires` side condition
        - Check postconditions (if present and not skipped)
        - Restore the environment from the `<fstack>`
        - Propagate the return value and the continuation `K`
 */
rule    <k> return V:Val; ~> _ 
                => 
                #if (Es =/=K .Ensures andBool notBool SkipCheck)
                #then
                        setSkipCheck(true) ~> setSkipPrint(true)
                        ~>
                        T RId = V;
                        forcePrintln("postcondition(s) of [ " + #toString(F)
                        + "(" + #toString(Vs) + ") ] check result : ");
                        forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                        ~> checkEnsures(1, Es)
                        ~>
                        forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                        ~> setSkipCheck(false) ~> setSkipPrint(false)
                #else
                    .K
                #fi
                ~> setEnv(Env) ~> V ~> K 
        </k>
        <control>
                <fstack> 
                        ListItem(fstackFrame(T',Env,K,function(F,_,_,_,_,Es
                        ,RId),Vs,Lstack,CrntObj)) 
                        => .List ...
                </fstack>
                <lstack> _ => Lstack </lstack>
                <estack> ListItem(_) => .List ... </estack>
                <returnType> T => T' </returnType>
                <crntObj> _ => CrntObj </crntObj>
        </control>
        <skipCheck> SkipCheck </skipCheck>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(V), T, IMap)

endmodule