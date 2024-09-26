/**
    This file defines the syntax for maps and entries
 */
module MMAP-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports AUXILIARY-SYNTAX
    imports MSET-SYNTAX

syntax ContainerType ::= "map" "<" Type "," Type ">" 
syntax Val ::= map(Type,Type,Address)

syntax Type ::=  "entry" "<" Type "," Type ">"
syntax Entry ::= "entry" "<" Val "," Val ">" 
syntax Val ::= Entry
syntax Entry ::= makeEntry(Val,Val)

syntax KItem ::= mapRawPut(Exp,Exp,Address)                [seqstrict(1,2)]
        | mapRawGet(Exp,Type,Address)                      [seqstrict(1)]
        | mapRawRemove(Exp,Address)                        [seqstrict(1)]

/**
    Function to search for a key in a list
    Params:
        - Val: Key to search for
        - List: List to search in
        - String: Operation type ("put" or "get")
 */
syntax Exp ::= searchSameKey(Val,List,String)               [function]

/** 
    Function to convert a Map to a Set of entries
    Params:
        - Map: Map to convert
 */
syntax Set ::= Map2EntrySet(Map)                            [function]

endmodule

module MMAP
    imports MMAP-SYNTAX
    imports DOMAINS
    imports CONFIGURATION

// Auxiliary Operations
rule typeOf(map(KType:Type, VType:Type, _:Address)) => map < KType, VType >
rule typeOf(entry<K:Val,V:Val>) => entry < typeOf(K), typeOf(V) >
rule typeToString(map < KType:Type , VType:Type >) 
        => "map<" +String typeToString(KType) +String "," +String typeToString(VType) +String ">"
rule typeToString(entry < KType:Type , VType:Type >) 
        => "entry<" +String typeToString(KType) +String "," +String typeToString(VType) +String ">"

rule Map2EntrySet(.Map) => .Set
rule Map2EntrySet((K:Val |-> V:Val) RestMap:Map) => SetItem(entry< K, V >) Map2EntrySet(RestMap)

rule    <k> map(_:Type, _:Type, address(A)).size() => size(M) ... </k>
        <store> ... A |-> M:Map ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> entry < KType, VType > X:Id; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> ... 
                .Map => A |-> undefined(entry < KType, VType >) 
                ... 
        </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Map Declaration
rule    <k> map<KType:Type, VType:Type> X:Id ; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> 
            ... 
                (.Map => A |-> map(KType, VType, address(A +Int 1))) 
                (.Map => (A +Int 1) |-> (.Map)) 
            ... 
        </store>
        <nextAddress> A => A +Int 2 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Map put
rule makeEntry(K:Val, V:Val) => entry < K, V >
rule searchSameKey(K, .List, "put") => K                   
rule searchSameKey(_, .List, "get") => nothing(void)

rule searchSameKey(K:Val, _:List, "put") => K
    requires notBool isObjectReference(K)
rule searchSameKey(K:Val, L:List, "get") => K in L ? K : nothing(void)
    requires notBool isObjectReference(K)
rule searchSameKey(K, ListItem(K') L:List, "put") 
    => K.String2Id("equals")(K') ? K' : searchSameKey(K, L, "put")
    requires isObjectReference(K)
rule searchSameKey(K, ListItem(K') L:List, "get") 
    => K.String2Id("equals")(K') ? K' : searchSameKey(K, L, "get")
    requires isObjectReference(K)   

rule    <k> mapRawPut(K:Val, V:Val, address(A)) => makeEntry(K,V) ... </k>
        <store> ... A |-> (M:Map => M[K <- V]) ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> map(KType, VType, address(A)).put(K:Val,V:Val) 
                => mapRawPut(searchSameKey(K, keys_list(M), "put"), 
                V, address(A)) ...
        </k>
        <store> ... A |-> M:Map ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf((getDeclaredType(K), getDeclaredType(V)), (KType, VType), IMap)

// Map get
rule    <k> mapRawGet(K:Val, VType:Type, address(A)) 
            =>
            #if K ==K nothing(void)
            #then undefined(VType)
            #else
                #if notBool isObjectReference(M[K])
                #then M[K]
                #else modifyDeclaredType({VType}:>Id, M[K])
                #fi
            #fi
            ... 
        </k>
        <store> ... A |-> M:Map ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> map(KType, VType, address(A)).get(K:Val) 
                => mapRawGet(searchSameKey(K, keys_list(M), "get"), 
                VType, address(A)) ...
        </k>
        <store> ... A |-> M:Map ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(K), KType, IMap)

// Map remove
rule    <k> mapRawRemove(K:Val, address(A)) 
            => K =/=K nothing(void)
            ... 
        </k>
        <store> 
            ... A |-> (M:Map => M[K <- undef]) ... 
        </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> map(KType, _, address(A)).remove(K:Val) 
                => mapRawRemove(searchSameKey(K, keys_list(M), "get"), 
                    address(A))
                ...
        </k>
        <store> ... A |-> M:Map ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(K), KType, IMap)

// Map containsKey
rule    <k> map(KType, _, address(A)).containsKey(K:Val) 
                => searchSameKey(K, keys_list(M), "get")
                    =/=K nothing(void)
                ...
        </k>
        <store> ... A |-> M:Map ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(K), KType, IMap)

// Map getOrDefault
rule    <k> map(KType, VType, address(A)).getOrDefault(K:Val, DefaultValue:Val) 
                => searchSameKey(K, keys_list(M), "get") == nothing(void) ? 
                DefaultValue : map(KType, VType, address(A)).get(K)
                ...
        </k>
        <store> ... A |-> M:Map ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(K), KType, IMap)

// Map entrySet
rule    <k> map(KType, VType, address(L)).entrySet() 
                => set(entry < KType, VType >, address(A))
                ...
        </k>
        <store> 
            ... 
                (L |-> M:Map)
                (.Map => A |-> Map2EntrySet(M)) 
            ... 
        </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Map isEmpty
rule    <k> map(_:Type, _:Type, address(A)).isEmpty() => size(M) ==Int 0 ... </k>
        <store> ... A |-> M:Map ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Entry getKey
rule    <k> entry<K, _>.getKey() => K ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Entry getValue
rule    <k> entry<_, V>.getValue() => V ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

endmodule