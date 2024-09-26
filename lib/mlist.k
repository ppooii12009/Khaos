/**
    This file defines the syntax for lists
 */
module MLIST-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports AUXILIARY-SYNTAX

// We define abstract list type to handle for temporary used variables, 
// or those lists not specified content types
syntax AbstractListType ::= "#AbstractListType"
syntax ContainerType ::= ListType
syntax ListType ::= "list" "<" Type ">"   
                    | AbstractListType

syntax Val ::= list(Type,Address)
                    | "#AbstractList"

endmodule

module MLIST
    imports MLIST-SYNTAX
    imports DOMAINS
    imports CONFIGURATION

// Auxiliary Operations
rule typeOf(list(T:Type, _:Address)) => list < T >
rule typeOf(list(#anyType, _:Address)) => #AbstractListType     [priority(0)]
rule typeOf(#AbstractList) => #AbstractListType
rule defaultValue(#AbstractListType) => #AbstractList
rule typeToString(list < T:Type >) => "list<" +String typeToString(T) +String ">"

rule    <k> list(_:Type, address(A)).size() => size(L) ... </k>
        <store> ... A |-> L:List ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule typeEquals(_:AbstractListType, list<_:Type>) => true
rule typeEquals(list<_:Type>, _:AbstractListType) => true

rule subtypeOf(list<_:Type>, _:AbstractListType, _:Map) => true
rule subtypeOf(_:AbstractListType, list<_:Type>, _:Map) => true

rule typeDifference(_:ListType, _:AbstractListType, _:Map) => 1
    [priority(1)]
rule typeDifference(_:AbstractListType, _:ListType, _:Map) => 1
    [priority(1)]

// List Declaration
rule    <k> list<T:Type> X:Id ; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> 
            ... 
                (.Map => A |-> list(T, address(A +Int 1))) 
                (.Map => (A +Int 1) |-> (.List)) 
            ... 
        </store>
        <nextAddress> A => A +Int 2 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> _:AbstractListType X:Id ; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> 
            ... 
                (.Map => A |-> #AbstractList) 
            ... 
        </store>
        <nextAddress> A => A +Int 1 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// List add
rule    <k> list(T, address(A)).add(V:Val) 
                => true ...
        </k>
        <store> ... A |-> (L:List => (L ListItem(V))) ... </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires subtypeOf(getDeclaredType(V), T, IMap)

rule    <k> list(T, address(A)).add(I:Int, V:Val) 
                => 
                #if I >=Int 0 andBool I <=Int size(L)
                #then true 
                #else runtimeError("Index out of bound")
                #fi 
                ...
        </k>
        <store> 
            ...
                A |-> (L:List => 
                    #if I >=Int 0 andBool I <=Int size(L)
                    #then 
                        (range(L, 0, size(L) -Int I) ListItem(V) range(L, I, 0))
                    #else
                        L
                    #fi
                    ) 
            ... 
        </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires subtypeOf(getDeclaredType(V), T, IMap)

//List get
rule    <k> list(T:Type, address(A)).get(I:Int) 
                => 
                #if I >=Int 0 andBool I <Int size(L)
                #then 
                    #if notBool isObjectReference(L[I])
                    #then L[I]
                    #else modifyDeclaredType({T}:>Id, L[I])
                    #fi
                #else runtimeError("Index out of bound")
                #fi
                ...
        </k>
        <store> ... A |-> L:List ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

// List remove
rule    <k> list(_, address(A)).remove(I:Int) 
                =>
                #if I >=Int 0 andBool I <=Int size(L)
                #then true 
                #else runtimeError("Index out of bound")
                #fi 
                ...
        </k>
        <store> 
            ...
                A |-> (L:List => 
                    #if I >=Int 0 andBool I <=Int size(L)
                    #then 
                        range(L, 0, size(L) -Int I) range(L, I +Int 1, 0)
                    #else
                        L
                    #fi
                ) 
            ... 
        </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires I >=Int 0 andBool I <Int size(L)

// List isEmpty
rule    <k> list(_:Type, address(A)).isEmpty() => size(L) ==Int 0 ... </k>
        <store> ... A |-> L:List ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule list(_:Type, address(-1)).isEmpty() => true [anywhere]

endmodule