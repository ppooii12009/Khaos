/**
    This file defines the syntax for arrays
 */
module MARRAY-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports AUXILIARY-SYNTAX
    imports ARRAY-SYNTAX

syntax Type ::= Type "[" "]"

syntax Val ::= array(Type,Address,Int)

/** 
    Function to calculate the content type of a multi-dimensional array
    Params:
        - Type: Base type of the array
        - Int: Number of dimensions
 */
syntax Type ::= calculateArrayContentType(Type,Int)     [function]

syntax List ::= Arr2List(Array,Int,Int)                 [function]

endmodule

module MARRAY
    imports MARRAY-SYNTAX
    imports DOMAINS
    imports CONFIGURATION
    imports ARRAY

// Auxiliary Operations
rule typeOf(array(T,_,_)) => (T[])
rule typeToString(T:Type []) => typeToString(T) +String "[]"
rule array(_,_,N).size() => N

rule calculateArrayContentType(T:Type,0) => T
rule calculateArrayContentType(T:Type,1) => T
rule calculateArrayContentType(T:Type,2) => T[]
rule calculateArrayContentType(T:Type,D:Int) =>
    calculateArrayContentType(T[],D -Int 1)
    requires D >=Int 3

rule Arr2List(Arr:Array, InclusiveStart:Int, ExclusiveEnd:Int)
    => ListItem(Arr[InclusiveStart]) Arr2List(Arr, InclusiveStart +Int 1, ExclusiveEnd)
    requires InclusiveStart <Int ExclusiveEnd
rule Arr2List(_:Array, InclusiveStart:Int, ExclusiveEnd:Int)
    => .List
    requires InclusiveStart >=Int ExclusiveEnd

// One-Dimension Array Declaration
rule    <k> T:Type X:Id[N:Int]; => .K ...</k>
        <env> Env => Env[X <- address(A)] </env>
        <store> 
            ... 
                (.Map => A |-> array(T, address(A +Int 1), N)) 
                (.Map => (A +Int 1) |-> fillArray(makeArray(N, defaultValue(T)), 0, N, defaultValue(T))) 
            ... 
        </store>
        <nextAddress> A => A +Int 2 </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires N >=Int 0

// Multi-Dimension Array Declaration
rule    <k> T:Type X:Id[N1:Int, N2:Int, Vs:Vals]; 
                =>  calculateArrayContentType(T,lengthOf(N1,N2,Vs)) X[N1];
                for(int tmpIdentifier(X,"_I")=0; tmpIdentifier(X,"_I") <= N1 - 1; ++tmpIdentifier(X,"_I")) 
                {
                        T tmpIdentifier(X,"_D")[N2,Vs];
                        X[tmpIdentifier(X,"_I")] = tmpIdentifier(X,"_D");
                }
                ...
        </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

context _:Type _::Exp[HOLE::Exps];
context _[HOLE::Exp, _] = _

rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs] [anywhere]

rule    <k> array(T:Type, address(A), L:Int)[N:Int] 
            => #if N >=Int 0 andBool N <Int L 
                #then
                    #if notBool isObjectReference(V[N])
                    #then V[N]
                    #else modifyDeclaredType({T}:>Id, V[N])
                    #fi 
                #else 
                    runtimeError("Array index out of bound")
                #fi
                ...
        </k>
        <store> ... A |-> V:Array ... </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

// Array Assignment
context HOLE:Exp[_] = _
context _[_] = HOLE
rule    <k> array(T:Type, address(A), L:Int)[N:Int] = V:Val 
            => #if N >=Int 0 andBool N <Int L 
                #then V
                #else 
                    runtimeError("Array index out of bound")
                #fi
                ...
        </k>
        <store> 
            ... 
                A |-> (Arr:Array => 
                    #if N >=Int 0 andBool N <Int L 
                    #then Arr[N <- V] 
                    #else Arr
                    #fi) 
            ... 
        </store>
        <inheritanceMap> IMap </inheritanceMap>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires subtypeOf(getDeclaredType(V), T, IMap)

endmodule