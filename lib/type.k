/**
    This file defines the syntax for types
 */
module TYPE-SYNTAX
    imports DOMAINS-SYNTAX
    
// Types
syntax NonContainerType ::= "void" | "int" | "bool" | "string" | Id
                    | "pointer"
syntax ContainerType
syntax AnyType ::= "#anyType"
syntax Type ::= NonContainerType 
                | ContainerType
                | AnyType
                | "(" Type ")"           [bracket]
syntax Types ::= List{Type,","}
syntax ANSIColorCode ::= ANSIColor(String)

endmodule

module TYPE
    imports TYPE-SYNTAX

endmodule