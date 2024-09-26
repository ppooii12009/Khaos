/**
    This file defines the syntax for expressions and basic values
 */
module EXP-SYNTAX
    imports DOMAINS-SYNTAX
    imports MAP

// Basic values
syntax Val ::= Int | Bool | String
syntax Vals ::= List{Val,","}               [overload(exps)]
syntax KResult ::= Val
syntax KResult ::= Vals

// Address values

/**
    Syntax declaration for address (pointer)
    Params:
        - Int: The `key` of the entry corresponding to the element in `<store>`
 */
syntax Address ::= address(Int)
syntax Val ::= Address

// Object values

/**
    Syntax declaration for object reference
    Params:
        - Id: Declared type (declared class name)
        - Id: Actual type (actual class name)
        - Address: Address of the object
 */
syntax ObjectReference ::= object(Id,Id,Address)

/**
    Syntax declaration for object members
    Params:
        - Id: Class name (the name of the class that actually has these members)
        - Map: Member variables
        - Map: Member functions
 */
syntax ObjectMember ::= objectMember(Id,Map,Map)
syntax Val ::=  ObjectReference | ObjectMember

// Expressions
syntax Exp ::= Val 
                | Id
                | "this"                                 
                | "super"                                
                | "(" Exp ")"               [bracket]
                | Exp "instanceOf" Id       [strict(1)]          
                | Exp "." Id                [group(exp-p2),strict(1)]     
                | Exp "[" Exps "]"          [group(exp-p2),seqstrict]
                | Exp "(" Exps ")"          [group(exp-p2),strict(2)]  
                | "invoke" "(" Exps ")"     [group(exp-p2),seqstrict] 
                | Exp "++"                  [group(exp-p2),left]
                | Exp "--"                  [group(exp-p2),left]
                | "++" Exp                  [group(exp-p3),right]
                | "--" Exp                  [group(exp-p3),right]
                | "!" Exp                   [group(exp-p3),right,seqstrict]
                | "-" Exp                   [group(exp-p3),right,seqstrict]
                | "&" Exp                   [group(exp-p3),right]
                | "*" Exp                   [group(exp-p3),right,seqstrict]
                | "new" Id "(" Exps ")"     [group(exp-p3),strict(2)] 
                | "(" Id ")" Exp            [group(exp-p3),strict(2)]
                | Exp "*" Exp               [group(exp-p5),left,seqstrict]
                | Exp "/" Exp               [group(exp-p5),left,seqstrict]
                | Exp "%" Exp               [group(exp-p5),left,seqstrict]
                | Exp "+" Exp               [group(exp-p6),left,seqstrict]
                | Exp "-" Exp               [group(exp-p6),left,seqstrict]
                | Exp "<<" Exp              [group(exp-p7),left,seqstrict]
                | Exp ">>" Exp              [group(exp-p7),left,seqstrict]
                | Exp "<" Exp               [group(exp-p8),left,seqstrict]
                | Exp "<=" Exp              [group(exp-p8),left,seqstrict]
                | Exp ">" Exp               [group(exp-p8),left,seqstrict]
                | Exp ">=" Exp              [group(exp-p8),left,seqstrict]
                | Exp "==" Exp              [group(exp-p9),left,seqstrict]
                | Exp "!=" Exp              [group(exp-p9),left,seqstrict]
                | Exp "&" Exp               [group(exp-p10),left,seqstrict]
                | Exp "^" Exp               [group(exp-p10),left,seqstrict]
                | Exp "|" Exp               [group(exp-p10),left,seqstrict]
                | Exp "&&" Exp              [group(exp-p13),left,strict(1)]
                | Exp "||" Exp              [group(exp-p14),left,strict(1)]
                | Exp "?" Exp ":" Exp       [group(exp-p15),right,strict(1)]
                | Exp "=" Exp               [group(exp-p15),right,strict(2)]
                | Exp "\n" Exp
                | Exp "\t" Exp

/**
    The operator precedence is referenced from 
    https://learn.microsoft.com/en-us/cpp/cpp/cpp-built-in-operators-precedence-and-associativity?view=msvc-170
 */
syntax priority  exp-p2 > exp-p3 > exp-p5 > exp-p6 > exp-p7
                > exp-p8 > exp-p9 > exp-p10 > exp-p13 > exp-p14 
                > exp-p15

syntax Exps ::= List{Exp,","}          [seqstrict, overload(exps)]
syntax Exps ::= Vals

endmodule

module EXP
    imports EXP-SYNTAX
    imports DOMAINS

/**
    Rules for basic arithmetic and logical operations
 */
rule - I:Int => 0 -Int I
rule I1:Int + I2:Int => I1 +Int I2
rule Str1 + Str2 => Str1 +String Str2
rule I1:Int - I2:Int => I1 -Int I2
rule I1:Int * I2:Int => I1 *Int I2
rule I1:Int / I2:Int => I1 /Int I2 requires I2 =/=K 0
rule I1:Int % I2:Int => I1 %Int I2 requires I2 =/=K 0
rule I1:Int << I2:Int => I1 <<Int I2
rule I1:Int >> I2:Int => I1 >>Int I2
rule I1:Int < I2:Int => I1 <Int I2
rule I1:Int <= I2:Int => I1 <=Int I2
rule I1:Int > I2:Int => I1 >Int I2
rule I1:Int >= I2:Int => I1 >=Int I2
rule V1:Val == V2:Val => V1 ==K V2
rule V1:Val != V2:Val => V1 =/=K V2
rule I1:Int & I2:Int => I1 &Int I2
rule I1:Int ^ I2:Int => I1 xorInt I2
rule I1:Int | I2:Int => I1 |Int I2
rule Str:String + I:Int => Str +String Int2String(I)
rule I:Int + Str:String => Int2String(I) +String Str
rule Str:String + B:Bool => Str +String Bool2String(B)
rule B:Bool + Str:String => Bool2String(B) +String Str
rule Str:String + address(L:Int):Address => Str +String Int2String(L)
rule address(L:Int):Address + Str:String => Int2String(L) +String Str
rule ! T => notBool(T)
rule true  && E => E
rule false && _ => false
rule true  || _ => true
rule false || E => E

context true ? HOLE::Exp : _
context false ? _ : HOLE::Exp
rule true ? E : _ => E
rule false ? _ : E => E

endmodule