/**
    This file defines the syntax for statements
 */
module STMT-SYNTAX
    imports DOMAINS-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports SPECIFICATION-SYNTAX

syntax Id ::= "Object" [token] | "main" [token]
            | "_RESULT_" [token]

// Declarations
syntax Parameter ::= Type Id
syntax Parameters ::= List{Parameter,","}
syntax Stmt ::= Type Exps ";" [avoid]      
                | Type Id "(" Parameters ")" Specifications Block   [macro]
                | Type Id "(" Parameters ")" ":" Id Specifications Block
                | "class" Id Block                
                | "class" Id "extends" Id Block

// Blocks
syntax Block ::= "{" "}"
                | "{" Stmt "}"

// Statements
syntax Stmt ::= Block
                | Exp ";"                               [seqstrict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block                [macro]
                | "while" "(" Exp ")" Invariants Block  
                | "for" "(" Stmt Exp ";" Exps ")" Invariants Block
                | "for" "(" Stmt Exp ";" Exps ")" Block [avoid,macro]
                | "for" "(" Stmt ";" Exps ")" Invariants Block      [avoid,macro]
                | "for" "(" Type Id ":" Exp ")" Invariants Block    [strict(3)]
                | "print" "(" Exps ")" ";"              [macro]
                | "print" "(" Exps "," ANSIColorCode "," ANSIColorCode ")" ";"    [strict(1)]
                | "println" "(" Exps ")" ";"            [macro]
                | "println" "(" Exps "," ANSIColorCode "," ANSIColorCode ")" ";"  [macro]
                | "return" Exp ";"                      [seqstrict]
                | "return" ";"
                | "spawn" Block
                | "continue" ";"
                | "break" ";"
                | "assert" Exp ";"                      
                | ";"                                   [avoid]
                | Stmt Stmt                             [right]
                | "<" Stmt ">"

endmodule

module STMT
    imports STMT-SYNTAX
    imports DOMAINS

// Desugaring macros
rule if (E) S => if (E) S else {}
rule for(Start::Stmt Condition::Exp; Step::Exps) {S} 
    => for(Start Condition; Step) .Invariants {S}
rule for(Start::Stmt ; Step::Exps) Invs:Invariants {S} 
    => for(Start true ; Step) Invs {S}
rule T::Type E1::Exp, E2::Exp, Es::Exps; => T E1; T E2, Es;           [anywhere]
rule T::Type X::Id = E; => T X; X = E;                                [anywhere]
rule println(E); => print(E); print("\n");
rule print(E); => print(E, ANSIColor("None"), ANSIColor("None"));
rule println(E, FColor:ANSIColorCode, BColor:ANSIColorCode); 
    => print(E, FColor, BColor); print("\n", FColor, BColor);

rule T::Type X::Id (Ps::Parameters) Ss:Specifications B:Block
    => T X (Ps) : _RESULT_ Ss B

rule class C:Id S => class C extends Object S

endmodule