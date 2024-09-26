/**
    This module defines the syntax for a simple version of lock
 */
module LOCK-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports DOMAINS-SYNTAX

/**
    Syntax declaration for lock type
        @ `mutex` ensures the locked memory can be only accessed by the lock holder
        @ `read-write` ensures read operation by other threads, but prohibits 
        write operation from others
        You can also add more types or modify the implemention here.
 */
syntax LockType ::= "mutex" | "read-write"

/**
    Syntax declaration for lock information
    Params:
        - Int: Thread ID of which holds the lock
        - Address: The locked memory address
        - String: Address of the object
 */
syntax Lock ::= lockItem(Int,Address,LockType)

/** 
    Syntax for lock type comparison
        The more strict lock is greater than less strict lock
 */
syntax Bool ::= LockType ">=LockType" LockType      [function]
/**
    Syntax for checking if a memory address is locked
    Params:
        - Address: Memory address to check
        - Set: Set of current locks
 */
                | isMemoryLocked(Address,Set)       [function]

syntax Stmt ::= "lock" "(" Address "," LockType ")" ";"
                | "lock" "(" Id ")" ";"             [macro]
                | "lock" "(" Id "," LockType ")" ";"
                | "unlock" "(" Id ")" ";"      
                | "unlock" "(" Address ")" ";"


endmodule

module LOCK
    imports LOCK-SYNTAX
    imports CONFIGURATION
    imports DOMAINS

/** 
    Default lock type is read-write when not specified
 */
rule lock(V:Id); => lock(V, read-write);

rule    <k> lock(V:Id, LT:LockType); => lock(A, LT); ... </k>
        <env> ... V |-> A:Address ... </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> unlock(V:Id); => unlock(A); ... </k>
        <env> ... V |-> A:Address ... </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Rules for lock type comparison
rule LT:LockType >=LockType LT => true
rule mutex >=LockType read-write => true
rule _ >=LockType _ => false    [owise]

// Rules for checking if memory is locked
rule isMemoryLocked(_:Address, .Set) => false
rule isMemoryLocked(A:Address, SetItem(lockItem(_, A, _))) => true
rule isMemoryLocked(A:Address, SetItem(lockItem(TID, A', LT)) Locks:Set)
    => isMemoryLocked(A, SetItem(lockItem(TID, A', LT)))
        orBool isMemoryLocked(A, Locks)
    [owise]

// Memory `A` has not been allocated
rule    <k> lock(address(A), _:LockType); 
            => runtimeError("Address [ " +String Int2String(A) +String " ] has not been allocated") 
            ... 
        </k>
        <store> Store </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires notBool A in_keys(Store)

// Memory has already been locked
rule    <k> lock(A, LT:LockType); 
            =>  #if LID ==Int TID
                #then   
                    #if LT >=LockType OLT
                    #then .K
                    #else runtimeError("High-level locks cannot be replaced with low-level locks : [ "
                        +String {OLT}:>String +String " -> " +String {LT}:>String +String " ]")
                    #fi
                #else lock(A, LT); 
                #fi
            ... 
        </k>
        <lock> SetItem(lockItem(LID, A, OLT)
                => #if LID ==Int TID andBool LT >=LockType OLT
                    #then lockItem(LID, A, LT)
                    #else lockItem(LID, A, OLT)
                    #fi
                ) 
            _:Set
        </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> DCnt => 
            #if LID ==Int TID #then 0 #else DCnt +Int 1 #fi
        </deadCounter>

// Memory has not been locked
rule    <k> lock(A, LT:LockType); => .K ... </k>
        <lock> Locks => Locks |Set SetItem(lockItem(TID, A, LT)) </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires notBool isMemoryLocked(A, Locks)

// Unlock memory
rule    <k> unlock(A:Address); => .K ... </k>
        <lock> SetItem(lockItem(TID, A, _)) => .Set ... </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

// Unlock memory
rule    <k> unlock(A:Address); => .K ... </k>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires notBool isMemoryLocked(A, Locks)

endmodule