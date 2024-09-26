module EXP-SYNTAX
    imports DOMAINS-SYNTAX
    imports TYPE-SYNTAX

// Basic values
syntax MyFloat ::= r"([\\+\\-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+\\-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
            | r"[\\+\\-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
            | r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]

syntax Dimension ::= "[" Int "]"

syntax Dimensions ::= List{Dimension,""}

syntax Val ::= Int | Bool | String | MyFloat
            | "new HashMap" "<" ">" "(" ")"
            | "new ArrayList" "<" ">" "(" ")"
            | "new HashSet" "<" ">" "(" ")"
            | "new" Type Dimensions

// Expressions
syntax Exp ::= Val 
                | Id
                | "this"                                 
                | "super"                                
                | "(" Exp ")"               
                | Exp "instanceOf" Id                
                | Exp "." Id                [group(exp-p2)]     
                | Exp "[" Exps "]"          [group(exp-p2),avoid]
                | Exp "(" Exps ")"          [group(exp-p2),avoid]  
                | Exp "++"                  [group(exp-p2),left]
                | Exp "--"                  [group(exp-p2),left]
                | "++" Exp                  [group(exp-p3),right]
                | "--" Exp                  [group(exp-p3),right]
                | "!" Exp                   [group(exp-p3),right]
                | "-" Exp                   [group(exp-p3),right]
                | "&" Exp                   [group(exp-p3),right]
                | "*" Exp                   [group(exp-p3),right]
                // Container operations
                | Exp ".add(" Exp ")"           [group(exp-p3)]
                | Exp ".remove(" Exp ")"        [group(exp-p3)]
                | Exp ".contains(" Exp ")"      [group(exp-p3)]
                | Exp ".size()"                 [group(exp-p3)]
                | Exp ".isEmpty()"              [group(exp-p3)]
                | Exp ".put(" Exp "," Exp ")"   [group(exp-p3)]
                | Exp ".get(" Exp ")"           [group(exp-p3)]
                | Exp ".containsKey(" Exp ")"   [group(exp-p3)]
                | Exp ".entrySet()"             [group(exp-p3)]
                // Below are for `Entry` type
                | Exp ".getKey()"               [group(exp-p3)]
                | Exp ".getValue()"             [group(exp-p3)]

// List
syntax Exp ::= Exp ".add(" Exp "," Exp ")"      [group(exp-p3)]
                //| Exp ".add(" Exp ")"           [strict,group(exp-p1)]
                //| Exp ".get(" Exp ")"           [strict,group(exp-p1)]
                //| Exp ".remove(" Exp ")"        [strict,group(exp-p1)]
                //| Exp ".size()"                 [group(exp-p3)]
                //| Exp ".isEmpty()"              [group(exp-p3)]

                | "new" Id "(" Exps ")"     [group(exp-p3)] 
                | "(" Type ")" Exp          [group(exp-p3)]
                | Exp "*" Exp               [group(exp-p5),left]
                | Exp "/" Exp               [group(exp-p5),left]
                | Exp "%" Exp               [group(exp-p5),left]
                | Exp "+" Exp               [group(exp-p6),left]
                | Exp "-" Exp               [group(exp-p6),left]
                | Exp "<<" Exp              [group(exp-p7),left]
                | Exp ">>" Exp              [group(exp-p7),left]
                | Exp "<" Exp               [group(exp-p8),left]
                | Exp "<=" Exp              [group(exp-p8),left]
                | Exp ">" Exp               [group(exp-p8),left]
                | Exp ">=" Exp              [group(exp-p8),left]
                | Exp "==" Exp              [group(exp-p9),left]
                | Exp "!=" Exp              [group(exp-p9),left]
                | Exp "&" Exp               [group(exp-p10),left]
                | Exp "^" Exp               [group(exp-p10),left]
                | Exp "|" Exp               [group(exp-p10),left]
                | Exp "&&" Exp              [group(exp-p13),left]
                | Exp "||" Exp              [group(exp-p14),left]
                | Exp "?" Exp ":" Exp       [group(exp-p15),right]
                | Exp "=" Exp               [group(exp-p15),right]

/**
    The operator precedence is referenced from 
    https://learn.microsoft.com/en-us/cpp/cpp/cpp-built-in-operators-precedence-and-associativity?view=msvc-170
 */
syntax priority  exp-p2 > exp-p3 > exp-p5 > exp-p6 > exp-p7
                > exp-p8 > exp-p9 > exp-p10 > exp-p13 > exp-p14 
                > exp-p15

syntax Exps ::= List{Exp,","}

syntax String ::= convertExp(Exp)                   [function]
syntax String ::= convertExps(Exps)                 [function]

syntax String ::= convertDimensions(Dimensions)     [function]
syntax Int ::= #length(Exps)                        [function]

syntax String ::= MyFloat2String(MyFloat) [function, hook(STRING.token2string)]

endmodule

module EXP
    imports EXP-SYNTAX
    imports TYPE
    imports DOMAINS

rule #length(.Exps) => 0
rule #length(_:Exp, Es:Exps) => 1 +Int #length(Es)

rule convertDimensions(.Dimensions) => ""
rule convertDimensions([I:Int] Rest:Dimensions) 
    => Int2String(I) +String ", " +String convertDimensions(Rest) 
    requires Rest =/=K .Dimensions
rule convertDimensions([I:Int]) => Int2String(I)

// Rules for convertExp function (basic values)
rule convertExp(I:Int) => Int2String(I)
rule convertExp(B:Bool) => Bool2String(B)
rule convertExp(S:String) => "\"" +String S +String "\""
rule convertExp(F:MyFloat) => MyFloat2String(F)

rule convertExp(new HashMap <> ()) => "map[]"
rule convertExp(new ArrayList <> ()) => "[]"
rule convertExp(new HashSet <> ()) => "{}"
rule convertExp(new T:Type Ds:Dimensions) => "new " +String convertType(T)
    +String "[" +String convertDimensions(Ds) +String "]"

// Rules for convertExp function (identifiers and keywords)
rule convertExp(X:Id) => Id2String(X)
rule convertExp(this) => "this"
rule convertExp(super) => "super"
rule convertExp((E:Exp)) => "(" +String convertExp(E) +String ")"

// Rules for convertExp function (unary operators)
rule convertExp(E:Exp ++) => convertExp(E = E + 1)
rule convertExp(E:Exp --) => convertExp(E = E - 1)
rule convertExp(++ E:Exp) => convertExp(E = E + 1)
rule convertExp(-- E:Exp) => convertExp(E = E - 1)
rule convertExp(! E:Exp) => "!" +String convertExp(E)
rule convertExp(- E:Exp) => "-" +String convertExp(E)
rule convertExp(& E:Exp) => "&" +String convertExp(E)
rule convertExp(* E:Exp) => "*" +String convertExp(E)

// Rules for convertExp function (binary operators)
rule convertExp(E:Exp instanceOf I:Id) => convertExp(E) +String " is " +String Id2String(I)
rule convertExp(E1:Exp * E2:Exp) =>  convertExp(E1) +String " * " +String convertExp(E2) 
rule convertExp(E1:Exp / E2:Exp) =>  convertExp(E1) +String " / " +String convertExp(E2) 
rule convertExp(E1:Exp % E2:Exp) =>  convertExp(E1) +String " % " +String convertExp(E2) 
rule convertExp(E1:Exp + E2:Exp) =>  convertExp(E1) +String " + " +String convertExp(E2) 
rule convertExp(E1:Exp - E2:Exp) =>  convertExp(E1) +String " - " +String convertExp(E2) 
rule convertExp(E1:Exp << E2:Exp) =>  convertExp(E1) +String " << " +String convertExp(E2) 
rule convertExp(E1:Exp >> E2:Exp) =>  convertExp(E1) +String " >> " +String convertExp(E2) 
rule convertExp(E1:Exp < E2:Exp) =>  convertExp(E1) +String " < " +String convertExp(E2) 
rule convertExp(E1:Exp <= E2:Exp) =>  convertExp(E1) +String " <= " +String convertExp(E2) 
rule convertExp(E1:Exp > E2:Exp) =>  convertExp(E1) +String " > " +String convertExp(E2) 
rule convertExp(E1:Exp >= E2:Exp) =>  convertExp(E1) +String " >= " +String convertExp(E2) 
rule convertExp(E1:Exp == E2:Exp) =>  convertExp(E1) +String " == " +String convertExp(E2) 
rule convertExp(E1:Exp != E2:Exp) =>  convertExp(E1) +String " != " +String convertExp(E2) 
rule convertExp(E1:Exp & E2:Exp) =>  convertExp(E1) +String " & " +String convertExp(E2) 
rule convertExp(E1:Exp ^ E2:Exp) =>  convertExp(E1) +String " ^ " +String convertExp(E2) 
rule convertExp(E1:Exp | E2:Exp) =>  convertExp(E1) +String " | " +String convertExp(E2) 
rule convertExp(E1:Exp && E2:Exp) =>  convertExp(E1) +String " && " +String convertExp(E2) 
rule convertExp(E1:Exp || E2:Exp) =>  convertExp(E1) +String " || " +String convertExp(E2) 

// Rules for convertExp function (ternary operator)
rule convertExp(E1:Exp ? E2:Exp : E3:Exp) => 
    "if " +String convertExp(E1) +String " then " +String convertExp(E2) +String " else " +String convertExp(E3)

// Rules for convertExp function (assignment operator)
rule convertExp(E1:Exp = E2:Exp) => convertExp(E1) +String " := " +String convertExp(E2)

// Rules for convertExp function (method calls and array access)
rule convertExp(E:Exp . X:Id) => convertExp(E) +String "." +String Id2String(X)
rule convertExp(E:Exp [ Es:Exps ]) => convertExp(E) +String "[" +String convertExps(Es) +String "]"
rule convertExp(E:Exp ( Es:Exps )) => convertExp(E) +String "(" +String convertExps(Es) +String ")"

// Rules for convertExp function (type casting)
rule convertExp(( T:Type ) E:Exp) => "(" +String convertType(T) +String ")" +String convertExp(E)

// Rules for convertExp function (object creation)
rule convertExp(new X:Id ( Es:Exps )) => 
    "new " +String Id2String(X) +String ".CONSTRUCTOR_" +String 
    Int2String(#length(Es)) +String "_PARAM(" +String 
    convertExps(Es) +String ")"

// Rules for convertExps function
rule convertExps(E:Exp, Rest:Exps) => convertExp(E) +String ", " +String convertExps(Rest)
    requires Rest =/=K .Exps
rule convertExps(E:Exp) => convertExp(E)
rule convertExps(.Exps) => ""

// Rules for convertExp function (container operations)
rule convertExp(E1:Exp .add(E2:Exp))
    => convertExp(E1) +String " := " +String convertExp(E1) +String
        " + { " +String convertExp(E2) +String " }"

rule convertExp(E1:Exp .remove(E2:Exp))
    => convertExp(E1) +String " := " +String convertExp(E1) +String 
    " - { " +String convertExp(E2) +String " }"

rule convertExp(E1:Exp .contains(E2:Exp)) 
    => convertExp(E2) +String " in " +String convertExp(E1)

rule convertExp(E:Exp .size()) => "|" +String convertExp(E) +String "|"

rule convertExp(E:Exp .isEmpty()) 
    => "|" +String convertExp(E) +String "| == 0"

rule convertExp(E:Exp .put(K:Exp, V:Exp)) 
    => convertExp(E) +String " := " +String convertExp(E) 
        +String "[ " +String convertExp(K) +String " := " +String 
        convertExp(V) +String " ]"

rule convertExp(E:Exp .get(K:Exp)) 
    => convertExp(E) +String "[" +String convertExp(K) +String "]"

rule convertExp(E:Exp .containsKey(K:Exp))
    => convertExp(K) +String " in " +String convertExp(E)

rule convertExp(E:Exp .entrySet()) => convertExp(E) +String ".Items"

// Rules for convertExp function (Entry type methods)
rule convertExp(E:Exp .getKey()) => convertExp(E) +String ".0"

rule convertExp(E:Exp .getValue()) => convertExp(E) +String ".1"

endmodule