/**
    This file handles `for` style and `while` style loops
    The process is : 
        - Convert `for` and `while` style loops into `loop` style loops
        - Push the corresponding environment into `<lstack>`
        - Rewrite `loop()` into `loopUnit()` and enter the loop
        - Execute `loopUnit` until it tells K framework to exit loop
        - Restore the environment from `<lstack>`
 */

module LOOP-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports SPECIFICATION-SYNTAX
    imports AUXILIARY-SYNTAX
    imports MARRAY-SYNTAX
    imports MLIST-SYNTAX
    imports MSET-SYNTAX
    imports MMAP-SYNTAX

/**
    Syntax declaration for normal loop unit (a round of loop)
    Params:
        - Exp: Condition expression
        - Stmt: Loop body
        - Exps: Iteration expressions
        - Invariants: Loop invariants
        - Bool: Whether to continue executing the current loop
            @ `true` to continue
            @ `false` to exit
 */
syntax LoopUnit ::= normalLoopUnit(Exp,Stmt,Exps,Invariants,Bool)
/**
    Syntax declaration for `foreach` loop unit (a round of loop)
    Params:
        - Id: Element variable name
        - Stmt: Loop body
        - List: List of elements to be traversed
        - Invariants: Loop invariants
        - Bool: Whether to continue executing the current loop
            @ `true` to continue
            @ `false` to exit
 */
                | foreachLoopUnit(Id,Stmt,List,Invariants,Bool)

/**
    Syntax declaration for normal loop (the whole loop)
    Params:
        - Exp: Condition expression
        - Stmt: Initialization statement
        - Exps: Iteration expressions
        - Stmt: Loop body
        - Invariants: Loop invariants
 */
syntax KItem ::= normalLoop(Exp,Stmt,Exps,Stmt,Invariants)
/**
    Syntax declaration for `foreach` loop (the whole loop)
    Params:
        - Type: Element type
        - Id: Element variable name
        - List: List of elements to be traversed
        - Stmt: Loop body
        - Invariants: Loop invariants
 */
                | foreachLoop(Type,Id,List,Stmt,Invariants)
                | LoopUnit
/** 
    Syntax declaration for information stored in loop stack `<lstack>`
    Params:
        - LoopUnit: Information about the loop being executed
        - Map: Environment before entering current loop layer
        - K: Program not completed before entering current loop layer
 */
                | lstackFrame(LoopUnit,Map,K)

endmodule

module LOOP
    imports LOOP-SYNTAX
    imports DOMAINS
    imports CONFIGURATION
    imports AUXILIARY
    imports COLLECTIONS

// `while` loop
rule    <k> while (Condition) Invs {Body::Stmt} 
                => normalLoop(Condition, ;, .Exps, Body, Invs) ...
        </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// `for` loop
rule    <k> for(Start Condition; Step) Invs {Body::Stmt} 
                => normalLoop(Condition, Start, Step, Body, Invs) ...
        </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// `foreach` loop
rule    <k> for(T:Type VName:Id : array(_:Type, address(A:Int), L:Int)) Invs {Body::Stmt} 
                =>
                foreachLoop(T, VName, Arr2List(Arr, 0, L), Body, Invs)
                ...
        </k>
        <store> ... A |-> Arr:Array ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> for(T:Type VName:Id : list(_:Type, address(A:Int))) Invs {Body::Stmt} 
                => 
                #if size(Elements) >Int 0
                #then foreachLoop(T, VName, Elements, Body, Invs)
                #else .K
                #fi
                ...
        </k>
        <store> ... A |-> Elements:List ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> for(T:Type VName:Id : set(_, address(A:Int))) Invs {Body::Stmt} 
                => 
                #if size(Elements) >Int 0
                #then foreachLoop(T, VName, Set2List(Elements), Body, Invs)
                #else .K
                #fi
                ...
        </k>
        <store> ... A |-> Elements:Set ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// rule    <k> for(T:Type VName:Id : map(_, _, address(A:Int))) Invs {Body::Stmt} 
//                 => 
//                 #if size(Elements) >Int 0
//                 #then foreachLoop(T, VName, Map2List(Elements), Body, Invs)
//                 #else .K
//                 #fi
//                 ...
//         </k>
//         <store> ... A |-> Elements:Map ... </store>
//         <id> TID </id>
//         <running> SetItem(TID) _:Set </running>

/**
    This rule is responsible for handling the work when entering a normal loop
    The process is: 
        - Push the information of the current loop and the unfinished program into `<lstack>`
        - Execute the initialization step `Start`
        - Decide whether to check the loop invariant based on the specific situation
        - Execute one iteration of the loop (`normalLoopUnit()`)
 */
rule    <k> normalLoop(Condition, Start, Step, Body, Invs) ~> K
                => 
                Start
                ~>
                #if (Invs =/=K .Invariants andBool notBool SkipCheck)
                #then
                    setSkipCheck(true) ~> setSkipPrint(true)
                    ~>
                    forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                    forcePrintln("loop invariants precheck : ");
                    ~> checkInvariants(1, Invs)
                    ~>
                    forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                    ~> setSkipCheck(false) ~> setSkipPrint(false)
                #else
                    .K
                #fi
                ~>
                normalLoopUnit(Condition, Body, Step, Invs, true)
        </k>
        <lstack> .List => 
                ListItem(lstackFrame(normalLoopUnit(Condition, Body, 
                        Step, Invs, true), Env, K)) 
                ... 
        </lstack>
        <env> Env </env>
        <skipCheck> SkipCheck </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    This rule is responsible for handling the work when entering a `foreach` loop
    The process is: 
        - Push the information of the current loop and the unfinished program into `<lstack>`
        - Declare element variable `VName`
        - Decide whether to check the loop invariant based on the specific situation
        - Execute one iteration of the loop (`foreachLoopUnit()`)
 */
rule    <k> foreachLoop(T, VName, Elements, Body, Invs) ~> K
                => 
                T VName = {Elements[0]}:>Exp ;
                ~>
                #if (Invs =/=K .Invariants andBool notBool SkipCheck)
                #then
                    setSkipCheck(true) ~> setSkipPrint(true)
                    ~>
                    forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                    forcePrintln("loop invariants precheck : ");
                    ~> checkInvariants(1, Invs)
                    ~>
                    forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                    ~> setSkipCheck(false) ~> setSkipPrint(false)
                #else
                    .K
                #fi
                ~>
                foreachLoopUnit(VName, Body, Elements, Invs, true)
        </k>
        <lstack> .List => 
                ListItem(lstackFrame(foreachLoopUnit(VName, Body, 
                        Elements, Invs, true), Env, K)) 
                ... 
        </lstack>
        <env> Env </env>
        <skipCheck> SkipCheck </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule defining the execution logic of a normal loop iteration
    The process is:
        - Check the loop condition
        - If condition is satisfied, execute the loop body `Body`
        - Execute the loop step expression `Step`
        - Check loop invariants (if needed)
        - Push the next iteration into kcell `<k>`
 */
rule    <k> normalLoopUnit(Condition, Body, Step, Invs, true)
                =>
                if(Condition)
                {
                    Body 
                    #hook(expsToStmt(Step))
                    if(Invs =/=K .Invariants andBool notBool SkipCheck)
                    {
                        #hook(setSkipCheck(true))
                        #hook(setSkipPrint(true))
                        forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                        forcePrintln("loop invariants in-loop check : ");
                        #hook(checkInvariants(1, Invs))
                        forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                        #hook(setSkipCheck(false))
                        #hook(setSkipPrint(false))
                    }
                    #hook(normalLoopUnit(Condition, Body, Step, Invs, true))
                }
                else
                {
                    #hook(normalLoopUnit(Condition, Body, Step, Invs, false))
                } ...
        </k>
        <skipCheck> SkipCheck </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule defining the execution logic of a `foreach` loop iteration
    The process is:
        - Pick next element and assign it to variable `VName`
        - Execute the loop body `Body`
        - Check loop invariants (if needed)
        - Push the next iteration into kcell `<k>`
        - Update the rest elements in `<lstack>`
 */
rule    <k> foreachLoopUnit(VName, Body, ListItem(Element) RestElements:List, Invs, true)
                =>
                {
                    typeOf(Element) VName = Element;
                    Body 
                    if(Invs =/=K .Invariants andBool notBool SkipCheck)
                    {
                        #hook(setSkipCheck(true))
                        #hook(setSkipPrint(true))
                        forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
                        forcePrintln("loop invariants in-loop check : ");
                        #hook(checkInvariants(1, Invs))
                        forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");
                        #hook(setSkipCheck(false))
                        #hook(setSkipPrint(false))
                    }
                    #hook(foreachLoopUnit(VName, Body, RestElements, Invs, true))
                } ...
        </k>
        <lstack> ListItem(lstackFrame(foreachLoopUnit(VName, Body, 
                        (_ => RestElements), Invs, true), _, _)) 
                ... 
        </lstack>
        <skipCheck> SkipCheck </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for exiting the loop
        Pops the loop information from the stack and restores the environment `<env>`
 */
rule    <k> normalLoopUnit(_, _, _, _, false) ~> _
                => K
        </k>
        <lstack> ListItem(lstackFrame(_ , Env, K)) => .List ... </lstack>
        <env> _ => Env </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> foreachLoopUnit(_, _, _, _, false) ~> _
                => K
        </k>
        <lstack> ListItem(lstackFrame(_ , Env, K)) => .List ... </lstack>
        <env> _ => Env </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> foreachLoopUnit(_, _, .List, _, _) ~> _
                => K
        </k>
        <lstack> ListItem(lstackFrame(_ , Env, K)) => .List ... </lstack>
        <env> _ => Env </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for the 'continue' statement
        Jumps to the next iteration of the current loop by retrieving the loop unit 
        from the stack `<lstack>`
 */
rule    <k> continue ; ~> _ => LU </k>
        <lstack> ListItem(lstackFrame(LU:LoopUnit, _, _)) ... </lstack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/**
    Rule for the 'break' statement
        Exits the current loop by mark 'loopUnit' with the 'false' flag.
 */
rule    <k> break ; ~> _ => normalLoopUnit(Condition, Body, Step, Invs, false) </k>
        <lstack> ListItem(lstackFrame(normalLoopUnit(
                        Condition, Body, Step, Invs, _), _, _)) ... 
        </lstack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> break ; ~> _ => foreachLoopUnit(VName, Body, Elements, Invs, false) </k>
        <lstack> ListItem(lstackFrame(foreachLoopUnit(
                    VName, Body, Elements, Invs, _:Bool), _, _)) ... 
        </lstack>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

endmodule