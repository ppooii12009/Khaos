/**
    This file defines the syntax for sets
 */
module MSET-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports AUXILIARY-SYNTAX

syntax ContainerType ::= "set" "<" Type ">"
syntax Val ::= set(Type,Address)

syntax KItem ::= setRawAdd(Exp,Exp,Address)                 [seqstrict(1,2)]
        | setRawRemove(Exp,Address)                         [seqstrict(1)]

/**
    Syntax for set value
    Params:
        - Type: Type of set elements
        - Address: Memory address of the set
 */
syntax Exp ::= searchSameElement(Val,Set)                    [function]

endmodule

module MSET
    imports MSET-SYNTAX
    imports DOMAINS
    imports CONFIGURATION

// Auxiliary Operations
rule typeOf(set(T:Type, _)) => set < T >
rule typeToString(set < T:Type >) => "set<" +String typeToString(T) +String ">"
rule    <k> set(_, address(A)).size() => size(S) ... </k>
        <store> ... A |-> S:Set ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule searchSameElement(_, .Set) => nothing(void)
rule searchSameElement(E:Val, SetItem(E) _:Set) => E
rule searchSameElement(E:Val, S:Set) => E in S ? E : nothing(void)
    requires notBool isObjectReference(E)
rule searchSameElement(E, SetItem(E') S:Set) 
    => E.String2Id("equals")(E') ? E' : searchSameElement(E, S) 

// Set Declaration
rule    <k> set<T:Type> X:Id ; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> 
            ... 
                (.Map => A |-> set(T, address(A +Int 1))) 
                (.Map => (A +Int 1) |-> (.Set)) 
            ... 
        </store>
        <nextAddress> A => A +Int 2 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Set add
rule    <k> setRawAdd(V:Val, SearchResult:Val, address(A)) 
            => SearchResult ==K nothing(void) 
            ... 
        </k>
        <store> 
            ... 
                A |-> (S:Set => 
                        #if SearchResult ==K nothing(void) 
                        #then S |Set SetItem(V) 
                        #else S 
                        #fi
                    ) 
            ... 
        </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> set(T, address(A)).add(V:Val) 
                => setRawAdd(V, searchSameElement(V, S), address(A))
                ...
        </k>
        <store> ... A |-> S:Set ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(V), T, IMap)

// Set remove
rule    <k> setRawRemove(V:Val, address(A)) 
            => V =/=K nothing(void)
            ...
        </k>
        <store> 
            ... 
                A |-> (S:Set =>
                        #if V =/=K nothing(void) 
                        #then  S -Set SetItem(V)
                        #else S 
                        #fi
                    ) 
            ... 
        </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> set(T, address(A)).remove(V:Val) 
                => setRawRemove(searchSameElement(V, S), address(A)) 
                ...
        </k>
        <store> ... A |-> S:Set ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(V), T, IMap)

// Set contains
rule    <k> set(T, address(A)).contains(V:Val) 
                => searchSameElement(V, S) =/=K nothing(void) ...
        </k>
        <store> ... A |-> S:Set ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(V), T, IMap)

// Set isEmpty
rule    <k> set(_, address(A)).isEmpty() => size(S) ==Int 0 ... </k>
        <store> ... A |-> S:Set ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

endmodule