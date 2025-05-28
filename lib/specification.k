/**
    This file defines the syntax for program specifications
 */
module SPECIFICATION-SYNTAX
    imports DOMAINS-SYNTAX
    imports EXP-SYNTAX

syntax Require ::= "requires" Exp                      
syntax Requires ::= List{Require,""}
syntax Ensure ::= "ensures" Exp                         
syntax Ensures ::= List{Ensure,""}
syntax Invariant ::= "invariant" Exp                   
syntax Invariants ::= List{Invariant,""}
syntax Specification ::= Require
                | Ensure
syntax Specifications ::= List{Specification,""}

// extract `requires` and `ensures` from specification list
syntax Requires ::= getRequires(Specifications,Requires)    [function]
syntax Ensures ::= getEnsures(Specifications,Ensures)       [function]

// reverse the `requires` and `ensures` list
// Due to the construction of the syntactic list, 
// the content extracted from `getRequires` and 
// `getEnsures` is in reverse order.
syntax Requires ::= reverseRequires(Requires, Requires) [function]
syntax Ensures ::= reverseEnsures(Ensures, Ensures) [function]

endmodule

module SPECIFICATION
    imports SPECIFICATION-SYNTAX

rule getRequires(.Specifications, Rs:Requires) 
    => reverseRequires(Rs, .Requires)
rule getRequires(R:Require S:Specifications, Rs:Requires) 
    => getRequires(S, R Rs)
rule getRequires(_:Ensure S:Specifications, Rs:Requires)
    => getRequires(S, Rs)
rule getEnsures(.Specifications, Es:Ensures) 
    => reverseEnsures(Es, .Ensures)
rule getEnsures(_:Require S:Specifications, Es:Ensures) 
    => getEnsures(S, Es)
rule getEnsures(E:Ensure S:Specifications, Es:Ensures)
    => getEnsures(S, E Es)

rule reverseRequires(.Requires, Ordered:Requires) => Ordered
rule reverseRequires(R:Require Unordered:Requires, Ordered:Requires) 
    => reverseRequires(Unordered, R Ordered)

rule reverseEnsures(.Ensures, Ordered:Ensures) => Ordered
rule reverseEnsures(E:Ensure Unordered:Ensures, Ordered:Ensures) 
    => reverseEnsures(Unordered, E Ordered)
endmodule
