module AUXILIARY-SYNTAX
    imports DOMAINS-SYNTAX
    imports CONFIGURATION-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports MAP
    imports LOCK-SYNTAX

syntax Stmt ::= #hook(KItem)
                | expsToStmt(Exps)

syntax KItem ::= undefined(Type)
                | defaultValue(Type)            [function]

syntax Type ::= typeOf(K)                       [function]
                | getDeclaredType(K)            [function]
                | getFirst(Types)               [function]

syntax Types ::= getTypes(Parameters)           [function]
                | getTypes(Vals)                [function]
                | findCloestSuperType(Types,List,Map,Int,Types)         [function]
                | getRest(Types)                [function]

syntax Val ::= nothing(Type)

syntax ObjectReference ::= modifyDeclaredType(Id,K) [function]

syntax Id ::= tmpIdentifier(Id,String)          [function]
                | typeToId(Type)                [function]

syntax String ::= #toString(K)                  [function]
                | valToString(Val)              [function]
                | valsToString(Vals)            [function]
                | expToString(Exp)              [function]
                | expsToString(Exps)            [function]
                | typeToString(Type)            [function]
                | typesToString(Types)          [function]

syntax Bool ::= isPrintable(Val)                [function]
                | subtypeOf(Types,Types,Map)    [function]
                | hasSuperTypeInList(Types,List,Map)                    [function]
                | isUndefined(K)                [function]
                | hasReadAccess(Int,Address,Set)        [function]
                | hasWriteAccess(Int,Address,Set)       [function]
                | typeEquals(Type,Type)         [function]

syntax ForegroundColor ::= String
syntax BackgroundColor ::= String
// Output Text, Front Color, Background Color
// All colors should be input using ANSI color codes
syntax String ::= colorText(String, ANSIColorCode, ANSIColorCode)      [function]

syntax KItem ::= setEnv(Map)
                | setGlobal(Bool)
                | setSkipCheck(Bool)
                | setStore(Map)
                | setSkipPrint(Bool)
                | setNextAddress(Int)
                | setCrntClass(Id)
                | setOccupied(Bool)
                | mkDecls(Parameters,Vals)  
                | checkRequire(Int,Require)
                | checkRequires(Int,Requires)    
                | checkEnsure(Int,Ensure)         
                | checkEnsures(Int,Ensures)         
                | checkAssert(String,Exp)
                | checkInvariant(Invariant)
                | checkInvariants(Int,Invariants)

syntax Int ::= getPureAddress(KItem)                    [function]
                | typeDifference(Types,Types,Map)       [function]
                | lengthOf(K)                           [function]
                | lengthOfTypes(Types)                  [function]
                | lengthOfVals(Vals)                    [function]
                | lengthOfExps(Exps)                    [function]
                | freshThreadId(Int)                    [function]

syntax Map ::= convertToMap(KItem)                      [function]
                | Int "..." Int "|->" K                 [function]

syntax Stmt ::= "forcePrint" "(" Exps ")" ";"              [seqstrict]
                | "forcePrintln" "(" Exps ")" ";"            [macro]

// Container operations
// Set
syntax Exp ::=  Exp ".add(" Exp ")"             [seqstrict,group(exp-p3)]
                | Exp ".remove(" Exp ")"        [seqstrict,group(exp-p3)]
                | Exp ".contains(" Exp ")"      [seqstrict,group(exp-p3)]
                | Exp ".size()"                 [seqstrict,group(exp-p3)]
                | Exp ".isEmpty()"              [seqstrict,group(exp-p3)]
// Map
syntax Exp ::=  Exp ".put(" Exp "," Exp ")"     [seqstrict,group(exp-p3)]
                | Exp ".get(" Exp ")"           [seqstrict,group(exp-p3)]
                //| Exp ".remove(" Exp ")"         [strict,group(exp-p1)]
                | Exp ".containsKey(" Exp ")"   [seqstrict,group(exp-p3)]
                | Exp ".getOrDefault(" Exp "," Exp ")"  [seqstrict,group(exp-p3)]
                | Exp ".entrySet()"             [seqstrict,group(exp-p3)]
                //| Exp ".size()"                 [seqstrict,group(exp-p3)]
                //| Exp ".isEmpty()"              [seqstrict,group(exp-p3)]
                // Below are for `Entry` type
                | Exp ".getKey()"               [seqstrict,group(exp-p3)]
                | Exp ".getValue()"             [seqstrict,group(exp-p3)]

// List
syntax Exp ::= Exp ".add(" Exp "," Exp ")"      [seqstrict,group(exp-p3)]
                //| Exp ".add(" Exp ")"           [strict,group(exp-p1)]
                //| Exp ".get(" Exp ")"           [strict,group(exp-p1)]
                //| Exp ".remove(" Exp ")"        [strict,group(exp-p1)]
                //| Exp ".size()"                 [seqstrict,group(exp-p3)]
                //| Exp ".isEmpty()"              [seqstrict,group(exp-p3)]

endmodule

module AUXILIARY
    imports AUXILIARY-SYNTAX
    imports DOMAINS
    imports CONFIGURATION
    imports TYPE
    imports EXP
    imports STMT

rule #hook(K:KItem) => K

rule expsToStmt(.Exps) => ;
rule expsToStmt(E:Exp) => E;
rule expsToStmt(E1:Exp, E2:Exp, Es:Exps) => E1; E2; ~> expsToStmt(Es)

rule tmpIdentifier(VName,Suffix) => String2Id(Id2String(VName) +String Suffix)

rule typeToId(T:Id) => T
rule typeToId(T:Type) => String2Id(typeToString(T))             [owise]

rule defaultValue(int) => 0
rule defaultValue(bool) => false
rule defaultValue(string) => ""
rule defaultValue(T:Type) => undefined(T)       [owise]

rule freshThreadId(I) => freshThreadId(!_:Int) 
   requires I <Int 0
rule freshThreadId(I:Int) => I +Int 1           
   requires I >=Int 0

rule N...M |-> _ => .Map  requires N >Int M
rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  requires N <=Int M

rule    {} => .K
rule    <k> { S } => S ~> setEnv(Env) ... </k>  
        <env> Env </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule S1:Stmt S2:Stmt => S1 ~> S2

rule    <k> ; => .K ... </k>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>


rule _:Val; => .K

rule mkDecls((T:Type X:Id, Ps:Parameters), (V:Val, Vs:Vals))
    => T X=V; ~> mkDecls(Ps,Vs)
rule mkDecls(.Parameters,.Vals) => {}

rule isUndefined(undefined(_:Type)) => true
rule isUndefined(_:K) => false [owise]

rule modifyDeclaredType(DClass:Id, object(_:Id, AClass:Id, A:Address))
    => object(DClass, AClass, A)

/** rules for configuration set operations start here **/
// only for those KItems with syntax like `set___()`

rule    <k> setEnv(Env) => .K ... </k>  
        <env> _ => Env </env>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
rule (setEnv(_) => .K) ~> setEnv(_)

rule    <k> setGlobal(B) => .K ... </k>
        <isGlobal> _ => B </isGlobal>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> setSkipCheck(B) => .K ... </k>
        <skipCheck> _ => B </skipCheck>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> setSkipPrint(B) => .K ... </k>
        <skipPrint> _ => B </skipPrint>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> setStore(Store) => .K ... </k>  
        <store> _ => Store </store>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
rule (setStore(_) => .K) ~> setStore(_)

rule    <k> setNextAddress(Next) => .K ... </k>  
        <nextAddress> _ => Next </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
rule (setNextAddress(_) => .K) ~> setNextAddress(_)

rule    <k> setCrntClass(C) => .K ... </k>
        <crntClass> _ => C </crntClass>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> setOccupied(B) => .K ... </k>
        <occupied> _ => B </occupied>

/** rules for configuration set operations end here **/



/** rules for getting length of syntactic list start here **/

rule S:String .size() => lengthString(S)

rule lengthOf(Vs:Vals) => lengthOfVals(Vs)
rule lengthOf(Es:Exps) => lengthOfExps(Es)
rule lengthOf(Ts:Types) => lengthOfTypes(Ts)

rule lengthOfVals(.Vals) => 0
rule lengthOfVals(_:Val) => 1
rule lengthOfVals(_:Val,_:Val,Vs:Vals) => 2 +Int lengthOfVals(Vs)

rule lengthOfExps(.Exps) => 0
rule lengthOfExps(_:Exp) => 1
rule lengthOfExps(_:Exp,_:Exp,Es:Exps) => 2 +Int lengthOf(Es)

/** rules for getting length of syntactic list end here **/



/** rules for checking specifications start here **/

context checkRequire(_:Int, requires HOLE::Exp)
context checkEnsure(_:Int, ensures HOLE::Exp)
context checkInvariant(invariant HOLE::Exp)
context checkAssert(_:String, HOLE::Exp)

rule checkRequire(I:Int, requires B:Bool) 
        => forcePrintln("\t" + "requires" + valToString(I) + " : " + B);
rule checkRequire(_:Int, _:Require) => false       [owise]
rule checkRequires(_:Int, .Requires) => .K
rule    <k> checkRequires(I:Int, R:Require) 
                => checkRequire(I, R) ~> setStore(STORE) 
                ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> checkRequires(I:Int, R1 R2 Rs) => checkRequire(I, R1) 
            ~> checkRequire(I +Int 1, R2) ~> checkRequires(I +Int 2, Rs) 
            ~> setStore(STORE) ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule checkEnsure(I:Int, ensures B:Bool) 
        => forcePrintln("\t" + "ensures" + valToString(I) + " : " + B);
rule checkEnsure(_:Int, _:Ensure) => false       [owise]
rule checkEnsures(_:Int, .Ensures) => .K
rule    <k> checkEnsures(I:Int, E:Ensure) 
                => checkEnsure(I, E) ~> setStore(STORE) 
                ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
rule    <k> checkEnsures(I:Int, E1 E2 Es) => checkEnsure(I, E1) 
            ~> checkEnsure(I +Int 1, E2) ~> checkEnsures(I +Int 2, Es) 
            ~> setStore(STORE) ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule checkInvariant(invariant B:Bool) => forcePrintln(B);
rule checkInvariants(_:Int, .Invariants) => .K
rule    <k> checkInvariants(I:Int, invariant E::Exp) 
                => forcePrint("\t" + "invariant" + valToString(I) + 
                " [ " + expToString(E) + " ] : ");
                ~> checkInvariant(invariant E) ~> setStore(STORE) 
                ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
rule    <k> checkInvariants(I:Int, invariant E1::Exp 
                invariant E2::Exp Invs) => 
            forcePrint("\t" + "invariant" + valToString(I) + 
                " [ " + expToString(E1) + " ] : ");    
            ~> checkInvariant(invariant E1) 
            ~> forcePrint("\t" + "invariant" + valToString(I +Int 1) + 
                " [ " + expToString(E2) + " ] : "); 
            ~> checkInvariant(invariant E2) 
            ~> checkInvariants(I +Int 2, Invs) 
            ~> setStore(STORE) ~> setNextAddress(NEXT) ...
        </k>
        <store> STORE </store>
        <nextAddress> NEXT </nextAddress>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule checkAssert(S:String,B:Bool) 
        => forcePrintln("-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=");
        forcePrintln("assertion [ " + S + " ] check result : " + B);
        forcePrintln("=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-");

/** rules for checking specifications end here **/



/** rules about types start here **/

rule typeOf(_:Int) => int
rule typeOf(_:Bool) => bool
rule typeOf(_:String) => string
rule typeOf(undefined(T)) => T
rule typeOf(nothing(T)) => T
rule typeOf(_:Address) => pointer
rule typeOf((T:Type _:Id):Parameter) => T

rule getDeclaredType(object(DT:Id, _, _)) => DT
rule getDeclaredType(Item:K) => typeOf(Item:K)          [owise]

rule getTypes(T:Type _:Id) => T, .Types
rule getTypes(T:Type _:Id, P, Ps) => T, getTypes(P,Ps)
rule getTypes(.Parameters) => void, .Types

rule getTypes(V:Val) => typeOf(V), .Types
rule getTypes(V1:Val, V2:Val, Vs:Vals) => typeOf(V1), getTypes(V2,Vs)
rule getTypes(.Vals) => void, .Types

//rule getFirst(.Types) => .Types
rule getFirst(T:Type, _:Types) => T

rule getRest(.Types) => .Types
rule getRest(_:Type, Ts:Types) => Ts

rule subtypeOf(T:Type, T, _) => true
rule subtypeOf(.Types, .Types, _) => true
rule subtypeOf(_:Type, _:AnyType, _) => true
rule subtypeOf(_:AnyType, _:Type, _) => true

rule subtypeOf(C1:Id, C:Id, M:Map C1 |-> C2:Id) => subtypeOf(C2, C, M)
        requires C1 =/=K C

rule subtypeOf(Object, Class:Id, _:Map) => false
        requires Class =/=K Object

rule subtypeOf((T:Type,Ts), (T':Type,Ts'), M:Map) 
        => subtypeOf(T, T', M) andBool subtypeOf(Ts, Ts', M)
        requires Ts =/=K .Types

rule subtypeOf(_:Types, _:Types, _:Map) => false          [owise]

rule hasSuperTypeInList(Ts:Types, TypeList:List, _:Map)
        => true
        requires Ts in TypeList

rule hasSuperTypeInList(_:Types, .List, _:Map) => false
rule hasSuperTypeInList(.Types, _:List, _:Map) => false
rule hasSuperTypeInList(Ts:Types, ListItem(Ts':Types) TL:List, IMap:Map)
        => subtypeOf(Ts, Ts', IMap)
        orBool hasSuperTypeInList(Ts, TL, IMap)

rule typeDifference(.Types, .Types, _:Map) => 0                 [priority(1)]
rule typeDifference(Ts:Types, Ts, _:Map) => 0                   [priority(1)]
rule typeDifference(Ts:Types, Ts':Types, _:Map) => 99999
        requires lengthOf(Ts) =/=Int lengthOf(Ts')
        [priority(1)]
rule typeDifference(C1:Id, C:Id, M:Map (C1 |-> C2:Id))
        => 1 +Int typeDifference(C2, C, M)
        requires C1 =/=K C
        [priority(1)]
rule typeDifference(Object, C:Id, _:Map) => 99999
        requires C =/=K Object
        [priority(1)]
rule typeDifference((T:Type, Ts:Types), (T':Type, Ts':Types), IMap:Map)
        => typeDifference(T, T', IMap) +Int typeDifference(Ts, Ts', IMap)
        requires Ts =/=K .Types andBool Ts' =/=K .Types
        [priority(2)]
rule typeDifference(_:Types, _:Types, _:Map) => 99999           [owise]

rule findCloestSuperType(Ts:Types, TypeList:List, _:Map, _:Int, _:Types) => Ts
        requires Ts in TypeList
rule findCloestSuperType(_:Types, .List, _:Map, _:Int, Result:Types) => Result
rule findCloestSuperType(Ts:Types, ListItem(Ts':Types) L:List, IMap:Map, D:Int, R:Types)
        => findCloestSuperType(Ts, L, IMap, D, R)
        requires typeDifference(Ts, Ts', IMap) >=Int D
rule findCloestSuperType(Ts:Types, ListItem(Ts':Types) L:List, IMap:Map, D:Int, _:Types)
        => findCloestSuperType(Ts, L, IMap, typeDifference(Ts, Ts', IMap), Ts')
        requires typeDifference(Ts, Ts', IMap) <Int D
rule findCloestSuperType(_:Types, _:List, _:Map, _:Int, _:Types) => .Types      [owise]

rule lengthOfTypes(.Types) => 0
rule lengthOfTypes(_:Type, Ts:Types) => 1 +Int lengthOfTypes(Ts)

rule typeEquals(T:Type, T':Type) => T ==K T'            [owise]

/** rules about types end here **/



/** rules for `#toString()` start here **/
rule #toString(V:Val) => valToString(V)
rule #toString(E:Exp) => expToString(E)
rule #toString(Vs:Vals) => valsToString(Vs)
rule #toString(Es:Exps) => expsToString(Es)
rule #toString(T:Type) => typeToString(T)
rule #toString(Ts:Types) => typesToString(Ts)
rule #toString(_:K) => "NOT PRINTABLE"                   [owise]

rule valToString(V:Int) => Int2String(V)
rule valToString(V:String) => V
rule valToString(V:Bool) => Bool2String(V)
rule valToString(address(I:Int):Address) => "address(" +String 
        Int2String(I) +String ")"
rule valToString(object(DClass:Id, AClass:Id, A:Address):ObjectReference)
        => "object(" +String Id2String(DClass) +String "," 
        +String Id2String(AClass) +String valToString(A)
        +String ")"

rule expToString(E:Val) => valToString(E::Val)
rule expToString(E:Id) => Id2String(E)
rule expToString(this) => "this"
rule expToString(E:Exp instanceOf I:Id) => expToString(E) +String "instanceOf"
        +String expToString(I)
rule expToString(E:Exp . I:Id) => expToString(E) +String "." 
        +String expToString(I)
rule expToString(E:Exp [ Es:Exps ]) => expToString(E) +String "["
        +String expsToString(Es) +String "]"
rule expToString(E:Exp ( Es:Exps )) => expToString(E) +String "("
        +String expsToString(Es) +String ")"
rule expToString(E:Exp ++) => expToString(E) +String "++"
rule expToString(E:Exp --) => expToString(E) +String "--"
rule expToString(++ E:Exp) => "++" +String expToString(E)
rule expToString(-- E:Exp) => "--" +String expToString(E)
rule expToString(! E:Exp) => "!" +String expToString(E)
rule expToString(- E:Exp) => "-" +String expToString(E)
rule expToString(& E:Exp) => "&" +String expToString(E)
rule expToString(* E:Exp) => "*" +String expToString(E)
rule expToString(new I:Id ( Es:Exps )) => "new" +String expToString(I)
        +String "(" +String expsToString(Es) +String ")"
rule expToString(( I:Id ) E:Exp) => "(" +String expToString(I)
        +String ")" +String expToString(E)
rule expToString(E1:Exp * E2:Exp) => expToString(E1) +String "*" 
        +String expToString(E2)
rule expToString(E1:Exp / E2:Exp) => expToString(E1) +String "/" 
        +String expToString(E2)
rule expToString(E1:Exp % E2:Exp) => expToString(E1) +String "%" 
        +String expToString(E2)
rule expToString(E1:Exp + E2:Exp) => expToString(E1) +String "+" 
        +String expToString(E2)
rule expToString(E1:Exp - E2:Exp) => expToString(E1) +String "-" 
        +String expToString(E2)
rule expToString(E1:Exp << E2:Exp) => expToString(E1) +String "<<" 
        +String expToString(E2)
rule expToString(E1:Exp >> E2:Exp) => expToString(E1) +String ">>" 
        +String expToString(E2)
rule expToString(E1:Exp < E2:Exp) => expToString(E1) +String "<" 
        +String expToString(E2)
rule expToString(E1:Exp <= E2:Exp) => expToString(E1) +String "<=" 
        +String expToString(E2)
rule expToString(E1:Exp > E2:Exp) => expToString(E1) +String ">" 
        +String expToString(E2)
rule expToString(E1:Exp >= E2:Exp) => expToString(E1) +String ">=" 
        +String expToString(E2)
rule expToString(E1:Exp == E2:Exp) => expToString(E1) +String "==" 
        +String expToString(E2)
rule expToString(E1:Exp != E2:Exp) => expToString(E1) +String "!=" 
        +String expToString(E2)
rule expToString(E1:Exp & E2:Exp) => expToString(E1) +String "&" 
        +String expToString(E2)
rule expToString(E1:Exp ^ E2:Exp) => expToString(E1) +String "^" 
        +String expToString(E2)
rule expToString(E1:Exp | E2:Exp) => expToString(E1) +String "|" 
        +String expToString(E2)
rule expToString(E1:Exp && E2:Exp) => expToString(E1) +String "&&" 
        +String expToString(E2)
rule expToString(E1:Exp || E2:Exp) => expToString(E1) +String "||" 
        +String expToString(E2)
rule expToString(E1:Exp = E2:Exp) => expToString(E1) +String "=" 
        +String expToString(E2)

rule valsToString(.Vals) => ""
rule valsToString(V:Val) => valToString(V)
rule valsToString(V1:Val, V2:Val, Vs:Vals)
        => valToString(V1) +String "," 
        +String valToString(V2) +String ","
        +String valsToString(Vs)
        requires Vs =/=K .Vals

rule valsToString(V1:Val, V2:Val, Vs:Vals)
        => valToString(V1) +String "," +String valToString(V2) 
        requires Vs ==K .Vals

rule expsToString(.Exps) => ""
rule expsToString(E:Exp)=> expToString(E)
rule expsToString(E1:Exp, E2:Exp, Es:Exps)
        => expToString(E1) +String "," 
        +String expToString(E2) +String ","
        +String expsToString(Es)
        requires Es =/=K .Exps

rule expsToString(E1:Exp, E2:Exp, Es:Exps)
        => expToString(E1) +String "," +String expToString(E2) 
        requires Es ==K .Exps

rule typeToString(void) => "void"
rule typeToString(int) => "int"
rule typeToString(bool) => "bool"
rule typeToString(string) => "string"
rule typeToString(pointer) => "pointer"
rule typeToString(ClassName:Id) => Id2String(ClassName)

rule typesToString(.Types) => ""
rule typesToString(T:Type)=> typeToString(T)
rule typesToString(T1:Type, T2:Type, Ts:Types)
        => typeToString(T1) +String "," 
        +String typeToString(T2) +String ","
        +String typesToString(Ts)
        requires Ts =/=K .Types

rule typesToString(T1:Type, T2:Type, Ts:Types)
        => typeToString(T1) +String "," +String typeToString(T2) 
        requires Ts ==K .Types

/** rules for `#toString()` end here **/

/** rules for printing start here **/

rule isPrintable(_:Int) => true
rule isPrintable(_:String) => true
rule isPrintable(_:Bool) => true
rule isPrintable(_:Address) => true
rule isPrintable(_:Val) => false [owise]

rule print(.Vals, _, _); => .K
rule forcePrint(.Vals); => .K
rule forcePrintln(E); => forcePrint(E); forcePrint("\n");

rule colorText(Text:String, ANSIColor(FColor), ANSIColor(BColor)) 
    => "\u001b[" +String FColor +String ";" +String BColor +String "m" 
       +String Text +String "\u001b[0m"
    requires FColor =/=String "None" andBool BColor =/=String "None"
rule colorText(Text:String, ANSIColor("None"), ANSIColor("None")) => Text

rule    <k> print(.Vals, _, _); => .K ... </k> 
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>

rule    <k> print((V:Val => V.String2Id("toString")(.Vals)), _:Exps, _, _); ...</k> 
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        requires notBool isPrintable(V)  [group(print)]

rule    <k> print(V:Val, Es, FColor, BColor); 
            =>  #write(FD, colorText(#toString(V) +String ",", FColor, BColor))
            ~>  print(Es, FColor, BColor); 
            ...
        </k> 
        <output>
            ... .List => ListItem(
                    colorText(#toString(V) +String ",", FColor, BColor)
                ) 
        </output>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <logFile> FD:Int </logFile>
        requires isPrintable(V) andBool Es =/=K .Exps [group(print)]

rule    <k> print(V:Val, .Exps, FColor, BColor); 
            =>  #write(FD, colorText(#toString(V), FColor, BColor)) 
            ...
        </k>
        <output>
            ... .List => ListItem(
                    colorText(#toString(V), FColor, BColor)
                ) 
        </output>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <logFile> FD:Int </logFile>
        requires isPrintable(V)  [group(print)]

rule    <k> forcePrint(V:Val, Es); 
            =>  #write(FD, colorText(#toString(V) +String ",", 
                    ANSIColor("34"), ANSIColor("43"))) 
            ~> forcePrint(Es) ;
            ...
        </k> 
        <output>
            ... .List => ListItem(
                    colorText(#toString(V) +String ",", 
                    ANSIColor("34"), ANSIColor("43"))
                ) 
        </output>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <logFile> FD:Int </logFile>
        requires isPrintable(V) andBool Es =/=K .Exps [group(print)]

rule    <k> forcePrint(V:Val, .Exps); 
            =>  #write(FD, colorText(#toString(V), ANSIColor("34"), 
                ANSIColor("43")))
            ...
        </k> 
        <output>
            ... .List => ListItem(
                    colorText(#toString(V), ANSIColor("34"), ANSIColor("43"))
                )
        </output>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <logFile> FD:Int </logFile>
        requires isPrintable(V)  [group(print)]

rule    <k> print(_:Exps, _, _); => .K ... </k>
        <skipPrint> true </skipPrint>
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>

rule    <k> V:Val .F:Id (.Vals) => #toString(V) ... </k> 
        <id> TID </id>
        <running> SetItem(TID) _:Set </running>
        <counter> Cnt => Cnt +Int 1 </counter>
        <deadCounter> _ => 0 </deadCounter>
        requires isPrintable(V)
            andBool F ==K String2Id("toString")

/** rules for printing end here **/

/** rules for memory access start here **/

rule hasReadAccess(TID:Int, A:Address, SetItem(lockItem(LID, A, mutex)) _:Set) 
    => false
    requires TID =/=Int LID
rule hasReadAccess(_:Int, _:Address, _:Set) => true     [owise]

rule hasWriteAccess(TID:Int, A:Address, SetItem(lockItem(LID, A, _)) _:Set)
    => TID ==Int LID
rule hasWriteAccess(_:Int, _:Address, _:Set) => true     [owise]

/** rules for memory access end here **/

rule getPureAddress(address(L)) => L

rule convertToMap(M:Map) => M                   [anywhere]

endmodule