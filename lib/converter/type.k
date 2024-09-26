module TYPE-SYNTAX
    imports DOMAINS-SYNTAX
    
// Types
syntax BasicType ::= "void" | "boolean" | "String"
                    | "byte" | "short" | "int" | "long"
                    | "float" | "double"

syntax ContainerType ::= "List" "<" Type ">"
                    | "Map" "<" Type "," Type ">"
                    | "Set" "<" Type ">"
                    | Type "[" "]"

syntax Type ::= BasicType
                | ContainerType
                | Id

syntax Types ::= List{Type,","}

syntax String ::= convertType(Type)                 [function]

endmodule

module TYPE
    imports TYPE-SYNTAX
    imports DOMAINS

// Basic type conversion rules
rule convertType(void) => "void"
rule convertType(boolean) => "bool"
rule convertType(String) => "string"
rule convertType(byte) => "int8"
rule convertType(short) => "int16"
rule convertType(int) => "int32"
rule convertType(long) => "int64"
rule convertType(float) => "real"
rule convertType(double) => "real"
// Used for user-defined classes
rule convertType(T:Id) => Id2String(T)

// Container type conversion rules
rule convertType(List<T:Type>) 
    => "seq<" +String convertType(T) +String ">"
rule convertType(Map<K:Type, V:Type>) 
    => "map<" +String convertType(K) +String ", " +String 
    convertType(V) +String ">"
rule convertType(Set<T:Type>) 
    => "set<" +String convertType(T) +String ">"
rule convertType(T:Type []) => "array<" +String convertType(T) +String ">"

endmodule