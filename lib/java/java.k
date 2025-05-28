module JAVA-SYNTAX
    imports DOMAINS-SYNTAX
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

syntax Type ::= "String"    [macro]
            | "boolean"     [macro]
            | "Integer"     [macro]

syntax Exp ::= "List.of(" Exps ")"                      [seqstrict]

syntax List ::= valsToList(Vals)                        [function]

syntax ContainerType ::= "Map" "<" Type "," Type ">"    [macro]
            | "List" "<" Type ">"                       [macro]
            | "Set" "<" Type ">"                        [macro]

syntax Id ::= "ArrayList<>"                             [token]
            | "HashMap<>"                               [token]
            | "HashSet<>"                               [token]

syntax AccessModifier ::= "public" | "protected" | "private"

syntax Type ::= "Map.Entry" "<" Type "," Type ">"            [macro]

syntax Lambda ::= "(" Parameters ")" "->" Block

syntax ThreadClosure ::= thread(Int,Block,Map)

syntax Stmt ::= AccessModifier "class" Id Block           [macro] 
            | "static" "class" Id Block             [macro] 
            | "static" "class" Id "extends" Id Block             [macro]
            | AccessModifier Id "(" Parameters ")" Specifications Block    [macro]     
            | AccessModifier Id "(" Parameters ")" ":" Id Specifications Block    [macro]
            | AccessModifier Type Id "(" Parameters ")" Specifications Block           [macro]
            | AccessModifier Type Id "(" Parameters ")" ":" Id Specifications Block    [macro]         
            | "@Override" AccessModifier Type Id "(" Parameters ")" Specifications Block           [macro]
            | "@Override" AccessModifier Type Id "(" Parameters ")" ":" Id Specifications Block    [macro]
            | "System.out.println" "(" Exps ")" ";"         [macro]
            | "System.err.println" "(" Exps ")" ";"         [macro] 
            | "System.exit" "(" Int ")" ";"
            | "import" PackagePath ";"        
            | "Thread.yield()" ";"  
            | "Thread" Id "=" "new Thread" "(" Lambda ")" ";"
            | Id "." "start()" ";"
            | Id "." "join()" ";"

syntax PackagePath ::= Id
                | PackagePath "." Id
                | PackagePath "." "*"

endmodule

module JAVA
    imports JAVA-SYNTAX
    imports CONFIGURATION
    imports COLLECTIONS

rule String:Type => string
rule boolean:Type => bool
rule Integer:Type => int

rule _:AccessModifier class C:Id B:Block => class C B
rule static class C:Id B:Block => class C B
rule static class C:Id extends FC:Id B:Block => class C extends FC B
rule _:AccessModifier F:Id (Ps:Parameters) Ss:Specifications B:Block => void F (Ps) : _RESULT_ Ss B
rule _:AccessModifier F:Id (Ps:Parameters) : RId:Id Ss:Specifications B:Block => void F (Ps) : RId Ss B
rule _:AccessModifier T:Type F:Id (Ps:Parameters) Ss:Specifications B:Block => T F (Ps) : _RESULT_ Ss B
rule _:AccessModifier T:Type F:Id (Ps:Parameters) : RId:Id Ss:Specifications B:Block => T F (Ps) : RId Ss B
rule @Override _:AccessModifier T:Type F:Id (Ps:Parameters) Ss:Specifications B:Block => T F (Ps) : _RESULT_ Ss B
rule @Override _:AccessModifier T:Type F:Id (Ps:Parameters) : RId:Id Ss:Specifications B:Block => T F (Ps) : RId Ss B

rule Map< KType:Type, VType:Type > :ContainerType => map<KType, VType> 
rule List< T:Type > :ContainerType => list< T > 
rule Set< T:Type > :ContainerType => set< T > 
rule Map.Entry< KType:Type, VType:Type > :Type => entry<KType, VType> 

rule System.out.println(Es:Exps); => println(Es);
rule System.err.println(Es:Exps); => println(Es, ANSIColor("31"), ANSIColor("47"));
rule import _ ; => ;

rule valsToList(.Vals) => .List
rule valsToList(V:Val, Rest:Vals) => ListItem(V) valsToList(Rest)
    requires Rest =/=K .Vals
rule valsToList(V:Val) => ListItem(V)

rule    <k> new ArrayList<>(.Exps) => list(#anyType, address(-1)) ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [priority(1)]

rule    <k> new HashSet<>(.Exps) => set(#anyType, address(-1)) ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [priority(1)]
    
rule    <k> new HashMap<>(.Exps) => map(#anyType, #anyType, address(-1)) ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        [priority(1)]

rule    <k> 
            List.of(Vs:Vals) 
                => list(getFirst(getTypes(Vs)), address(A))
            ...
        </k>
        <store> 
            ... (.Map => A |-> valsToList(Vs)) ... 
        </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

// Empty list assignment
rule    <k> X:Id = list(#anyType, address(-1)) => list(T, address(L)) ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> list(T, _ => address(L)) 
                (.Map => L |-> .List)
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

rule    <k> *address(A) = list(#anyType, address(-1)) => list(T, address(L)) ... </k>
        <store> 
            ... 
                A |-> list(T, _ => address(L)) 
                (.Map => L |-> .List)
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

// Empty set assignment
rule    <k> X:Id = set(#anyType, address(-1)) => set(T, address(L)) ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> set(T, _ => address(L)) 
                (.Map => L |-> .Set)
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

rule    <k> *address(A) = set(#anyType, address(-1)) => set(T, address(L)) ... </k>
        <store> 
            ... 
                A |-> set(T, _ => address(L)) 
                (.Map => L |-> .Set)
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

// Empty map assignment
rule    <k> X:Id = map(#anyType, #anyType, address(-1)) => map(KType, VType, address(L)) ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> map(KType, VType, _ => address(L)) 
                (.Map => L |-> (.Map))
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

rule    <k> *address(A) = map(#anyType, #anyType, address(-1)) => map(KType, VType, address(L)) ... </k>
        <store> 
            ... 
                A |-> map(KType, VType, _ => address(L)) 
                (.Map => L |-> (.Map))
            ... 
        </store>
        <nextAddress> L => L +Int 1 </nextAddress>
        <lock> Locks </lock>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires hasWriteAccess(TID, address(A), Locks)
        [group(assignment), priority(0)]

// System.exit
rule    <k> System.exit(1); => .K ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set => .Set </running>
        <ready> RSet => .Set </ready>
        <suspended> _ => RSet </suspended>
        <statusCode> _ => 1 </statusCode>

// Thread.yield
rule    <k> Thread.yield(); => .K ... </k>
        <id> TID </id>
        <running> ... SetItem(TID) => .Set ... </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        // <errorMessage> EM => EM +String " [ thread " +String 
        //     Int2String(TID) +String " yield " +String 
        //     " when Counter = " +String Int2String(Cnt) +String " ] "
        // </errorMessage>

// create thread variable
rule    <k> Thread X:Id = new Thread((.Parameters) -> B:Block) ; => .K ... </k>
        <env> Env:Map => Env[X <- address(A)] </env>
        <store> 
            ... 
                .Map => A |-> thread(freshThreadId(!_:Int), B, Env)
            ... 
        </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

// start thread
rule    <k> X:Id . start() ; => .K ... </k>
        <estack> EStack </estack>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> thread(SonThreadId:Int, B:Block, Env:Map)
            ... 
        </store>
        <id> FatherThreadId:Int </id>
        (.Bag => 
            <thread>
                ...
                <k> B </k>
                <estack> EStack </estack>
                <env> Env </env>
                <id> SonThreadId </id>
                <isGlobal> false </isGlobal>
                <new> false </new>
                ...
            </thread>
        )
        <running> SetItem(FatherThreadId) _:Set </running>
        <ready> RSet => RSet |Set SetItem(SonThreadId) </ready>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

// join thread
rule    <k> X:Id . join() ; => .K ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> thread(TargetThreadId:Int, _, _)
            ... 
        </store>
        <id> CurrentThreadId:Int </id>
        <running> ... SetItem(CurrentThreadId) => .Set ... </running>
        <terminated> TerminatedSet:Set </terminated>
        <ready> ... SetItem(CurrentThreadId) => .Set ... </ready>
        <suspended> ... .Set => SetItem(CurrentThreadId) ... </suspended>
        <counter> Cnt => Cnt +Int 1 </counter>
        <blockMap>
            ... CurrentThreadId |-> (BlockSet:Set => BlockSet |Set SetItem(TargetThreadId)) ...
        </blockMap>
        requires notBool TargetThreadId in TerminatedSet

rule    <k> X:Id . join() ; => .K ... </k>
        <env> ... X |-> address(A) ... </env>
        <store> 
            ... 
                A |-> thread(TargetThreadId:Int, _, _)
            ... 
        </store>
        <id> CurrentThreadId:Int </id>
        <running> SetItem(CurrentThreadId) _:Set </running>
        <terminated> TerminatedSet:Set </terminated>
        <counter> Cnt => Cnt +Int 1 </counter>
        requires TargetThreadId in TerminatedSet

endmodule
