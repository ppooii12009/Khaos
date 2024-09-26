requires "./lib/configuration.k"
requires "./lib/type.k"
requires "./lib/exp.k"
requires "./lib/stmt.k"
requires "./lib/specification.k"
requires "./lib/auxiliary.k"
requires "./lib/mmap.k"
requires "./lib/marray.k"
requires "./lib/mset.k"
requires "./lib/mlist.k"
requires "./lib/loop.k"
requires "./lib/function.k"
requires "./lib/objectOriented.k"
requires "./lib/lock.k"
requires "./lib/java/java.k"
requires "./lib/java/jstringbuilder.k"

module LANGUAGE-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports SPECIFICATION-SYNTAX
    imports AUXILIARY-SYNTAX
    imports MMAP-SYNTAX
    imports MARRAY-SYNTAX
    imports MSET-SYNTAX
    imports MLIST-SYNTAX
    imports LOOP-SYNTAX
    imports FUNCTION-SYNTAX
    imports OBJECTORIENTED-SYNTAX
    imports LOCK-SYNTAX
    imports JAVA-SYNTAX
    imports JSTRINGBUILDER-SYNTAX


endmodule

module LANGUAGE
    imports LANGUAGE-SYNTAX
    imports DOMAINS
    imports COLLECTIONS
    imports CONFIGURATION
    imports TYPE
    imports EXP
    imports STMT
    imports SPECIFICATION
    imports AUXILIARY
    imports MMAP
    imports MARRAY
    imports MSET
    imports MLIST
    imports LOOP
    imports FUNCTION
    imports OBJECTORIENTED
    imports LOCK
    imports JAVA
    imports JSTRINGBUILDER

/** Declaration Start Here **/

// Variable Declaration
rule    <k> T:NonContainerType X:Id; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> ... .Map => A |-> defaultValue(T) ... </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/** Declaration End Here **/

/** Lookup Start Here **/

// Variable Lookup
rule    <k> X:Id => V ...</k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> V ... </store>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires hasReadAccess(TID, address(A), Locks)
        [group(lookup)]

/** Lookup End Here **/

/** Assignment Start Here **/

// Get Address
rule    <k> &X:Id => A ... </k>
        <env> ... X |-> A ... </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Dereference
rule    <k> *address(A) => V ... </k>
        <store> ... A |-> V ... </store>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires hasReadAccess(TID, address(A), Locks)

// Variable Assignment
rule    <k> X:Id = V:Val => V ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> (OldValue => V) ... </store>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires notBool isObjectReference(V)
                andBool typeEquals(typeOf(OldValue), typeOf(V))
                andBool hasWriteAccess(TID, address(A), Locks)
        [group(assignment)]

rule    <k> *address(L) = V:Val => V ... </k>
        <store> ... L |-> (OldValue => V) </store>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires notBool isObjectReference(V)
                andBool typeEquals(typeOf(OldValue), typeOf(V))
                andBool hasWriteAccess(TID, address(L), Locks)
        [group(assignment)]

rule A:Address = V:Val => *A = V

rule *(&(ITEM)) => ITEM   [anywhere]
rule &(*(ITEM)) => ITEM   [anywhere]
context *(HOLE::Exp) = _

/** Assignment End Here **/


/** `If` Statements Start Here **/

rule if ( true) S else _ => S
rule if (false) _ else S => S

/** `If` Statements End Here */


/** Auxiliary Operations Start Here **/

// Self-increment
rule    <k> ++X:Id => V +Int 1 ...</k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> (V => V +Int 1) ... </store>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(increment)]

rule    <k> X:Id ++ => V ...</k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> (V => V +Int 1) ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        <lock> Locks </lock>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(increment)]

// Self-decrement
rule    <k> --X:Id => V -Int 1 ...</k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> (V => V -Int 1) ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        <lock> Locks </lock>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(decrement)]

rule    <k> X:Id -- => V ...</k>
        <env> ... X |-> address(A) ... </env>
        <store> ... A |-> (V => V -Int 1) ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        <lock> Locks </lock>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(decrement)]

// rule    <k> ++array(_:Type, address(A), L:Int)[N:Int] => Arr[N] +Int 1 ...</k>
//         <store> ... A |-> (Arr => Arr[N <- (Arr[N] +Int 1)]) ... </store>
//         requires N >=Int 0 andBool N <Int L
//         [group(increment)]

/** Auxiliary Operations End Here **/

// Assert

// check assertions
rule    <k> assert E:Exp ; => 
                #if notBool SkipCheck
                #then 
                setSkipCheck(true) ~> setSkipPrint(true) 
                ~> checkAssert(expToString(E), E)
                ~> setSkipCheck(false) ~> setSkipPrint(false)
                ~> setEnv(Env) ~> setStore(Store) ~> setNextAddress(Next)
                #else .K
                #fi
                ... 
        </k>
        <env> Env </env>
        <store> Store </store>
        <nextAddress> Next </nextAddress>
        <skipCheck> SkipCheck </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

/** Multi-Thread Features Start Here **/

rule    <thread>
            ...
            <id> TID </id>
            <new> true => false </new>
            ...
        </thread>
        <ready> RSet => RSet |Set SetItem(TID) </ready>

rule    <thread>
                ...
                <k> spawn {S} => .K ...</k>
                <env> Env </env>
                <id> TID </id>
                ...
        </thread>
       (.Bag => 
                <thread>
                        ...
                        <k> S </k>
                        <env> Env </env>
                        <id> freshThreadId(!_:Int) </id>
                        <isGlobal> false </isGlobal>
                        ...
                </thread>
        )
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    (<thread> ... <k> .K </k> <id> T </id> ... </thread> => .Bag)
        <terminated> ... .Set => SetItem(T) ... </terminated>
        <ready> RSet => RSet -Set SetItem(T) </ready>
        <running> RSet' => RSet' -Set SetItem(T) </running>

/** Generate the next pseudo-random number using the linear congruential generator (LCG)
    The random number is generated as `(a * seed + c) % m`
    The constants we use are: 
        @ a = 1664525
        @ c = 1013904223
        @ m = 2147483648(2^32)
        @ These are constants used by GCC. You can also change the values here.
 */
rule    <running> .Set => SetItem(Set2List(RSet)[
            (1664525 *Int Seed +Int 1013904223) %Int 2147483648 %Int size(RSet)
            ])  
        </running>
        <ready> RSet </ready>
        <seed> Seed => (1664525 *Int Seed +Int 1013904223) %Int 2147483648 </seed>
        requires size(RSet) >Int 0

// Randomly schedule
rule    <running> SetItem(TId:Int) => SetItem(Set2List(RSet)[
            (1664525 *Int Seed +Int 1013904223) %Int 2147483648 %Int size(RSet)
            ])  
        </running>
        <ready> RSet </ready>
        <seed> Seed => (1664525 *Int Seed +Int 1013904223) %Int 2147483648 </seed>
        <counter> Cnt => Cnt +Int 1 </counter>
        <occupied> false </occupied>
        // <errorMessage> EM => EM +String " [ schedule from " +String 
        //     Int2String(TId) +String " to " +String Int2String({Set2List(RSet)[
        //     (1664525 *Int Seed +Int 1013904223) %Int 2147483648 %Int size(RSet)
        //     ]}:>Int) +String " when Counter = " +String Int2String(Cnt) +String " ] \n"
        // </errorMessage>
        requires size(RSet) >Int 0 
            andBool (Cnt %Int 5) ==Int 0

// Program successfully terminated
rule    <running> .Set </running>
        <ready> .Set </ready>
        <suspended> .Set </suspended> 
        <statusCode> 1 => 0 </statusCode>

// Atomic operation
rule    <k> < S:Stmt > => S ~> setOccupied(O) ... </k>
        <occupied> O => true </occupied>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Thread waiting
rule    <statusCode> 1 </statusCode>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> DCnt => DCnt +Int 1 </deadCounter>
        <maxDeadCounter> MDC => maxInt(MDC, DCnt +Int 1) </maxDeadCounter>
        <ready> ActiveThreads:Set </ready>
        requires DCnt <=Int (size(ActiveThreads) *Int 10)
        [owise]

// Deadlock detected
rule    <statusCode> 1 => 2 </statusCode>
        <deadCounter> DCnt </deadCounter>
        <running>  _ => .Set </running>
        <ready> ActiveThreads:Set => .Set </ready>
        <suspended> _ => ActiveThreads </suspended>
        <errorMessage> EM => 
            EM +String " [ " +String "Potential deadlock detected" +String " ] " 
        </errorMessage>
        requires DCnt >Int (size(ActiveThreads) *Int 10)
        [priority(0)]

/** Multi-Thread Features Start Here **/

endmodule
