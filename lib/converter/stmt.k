module STMT-SYNTAX
    imports DOMAINS-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports MAP

// Declarations
syntax Parameter ::= Type Id
syntax Parameters ::= List{Parameter,","}

syntax AccessModifier ::= "public" | "protected" | "private"
syntax NonAccessModifier ::= "static" | "final" | "abstract"
syntax Annotation ::= "@Override"
syntax Modifier ::= AccessModifier | NonAccessModifier | Annotation
syntax Modifiers ::= List{Modifier,""}

syntax Ids ::= List{Id,","}

// Blocks
syntax Block ::= "{" "}"
                | "{" Stmt "}"

// Statements
syntax Stmt ::= Block
                | VarDeclStmt
                | Modifiers VarDeclStmt
                | MethodDeclStmt
                | Modifiers MethodDeclStmt
                | ClassDeclStmt
                | Modifiers ClassDeclStmt
                | IfStmt
                | WhileStmt
                // ForStmt
                | "for" "(" Stmt Exp ";" Exps ")" Block     [macro]
                | "for" "(" Stmt ";" Exps ")" Block         [macro]
                | #expsToStmt(Exps)                     [function]
                | Exp ";"           
                | "return" Exp ";"
                | "return" ";"
                | "continue" ";"
                | "break" ";"
                | "assert" Exp ";"                      
                | ";"                                   [avoid]
                | Stmt Stmt                             [right]
                | "System.out.println(" Exp ")" ";"

syntax VarDeclStmt ::= Type Exps ";"                    [avoid]

syntax MethodDeclStmt ::= Type Id "(" Parameters ")" Block  [avoid]
                | Id "(" Parameters ")" Block           [avoid]

syntax ClassDeclStmt ::= "class" Id Block               [avoid]
                | "class" Id "implements" Ids Block     [avoid]
                | "interface" Id Block                  [avoid]
                | "interface" Id "extends" Id Block     [avoid]

syntax IfStmt ::= "if" "(" Exp ")" Block "else" Block   [avoid]
                | "if" "(" Exp ")" Block "else" IfStmt  [avoid]
                | "if" "(" Exp ")" Block

syntax WhileStmt ::= "while" "(" Exp ")" Block

syntax String ::= convertParameter(Parameter)           [function]
                | convertParameters(Parameters)         [function]
                | convertModifier(Modifier)             [function]
                | convertModifiers(Modifiers)           [function]
                | convertStmt(Stmt,Map)                 [function]
                | convertClassDeclStmt(Stmt,Map)        [function]
                | convertIds(Ids)                       [function]

syntax Bool ::= containModifier(Modifiers,Modifier)     [function]

syntax Int ::= #length(Parameters)                      [function]

endmodule

module STMT
    imports STMT-SYNTAX
    imports DOMAINS

rule #length(.Parameters) => 0
rule #length(_:Parameter, Ps:Parameters) => 1 +Int #length(Ps)

rule S1:Stmt S2:Stmt => S1 ~> S2

// Rules for convertParameter and convertParameters functions
rule convertParameter(T:Type V:Id) => 
    Id2String(V) +String ": " +String convertType(T)
rule convertParameters(P:Parameter, Rest:Parameters) =>
    convertParameter(P) +String "," +String convertParameters(Rest)
    requires Rest =/=K .Parameters
rule convertParameters(P:Parameter, Rest:Parameters) => convertParameter(P)
    requires Rest ==K .Parameters
rule convertParameters(.Parameters) => ""

// Rules for convertModifier and convertModifiers functions
rule convertModifier(static) => "static "
rule convertModifier(_:Modifier) => ""                      [owise]
rule convertModifiers(.Modifiers) => ""
rule convertModifiers(M:Modifier Ms:Modifiers) 
    => convertModifier(M) +String convertModifiers(Ms)

// Rules for convertIds function
rule convertIds(.Ids) => ""
rule convertIds(I:Id, Is:Ids) => 
    Id2String(I) +String ", " +String convertIds(Is)
    requires Is =/=K .Ids
rule convertIds(I:Id, .Ids) => Id2String(I)

// Rules for convertStmt function (Block)
rule convertStmt({ S:Stmt }, M:Map) => 
    "\n{\n" +String convertStmt(S, M) +String "}\n"
rule convertStmt({ }, _:Map) => "\n{}\n"

// Rules for convertStmt function (VarDeclStmt)
rule convertStmt(_:Modifiers S:VarDeclStmt, M:Map) => convertStmt(S, M)

rule convertStmt(_:Type .Exps ;, _:Map) => ""

rule convertStmt(T:Type X:Id ;, _:Map) => 
    "var " +String Id2String(X) +String ": " +String convertType(T) 
    +String ";\n"

rule convertStmt(T:Type X:Id = E:Exp ;, _:Map) => 
    "var " +String Id2String(X) +String ": " +String convertType(T) 
    +String " := " +String convertExp(E) +String ";\n"

rule convertStmt(T:Type E:Exp , Es:Exps ;, M:Map) => 
    convertStmt(T E ;, M) +String convertStmt(T Es ;, M)
    requires Es =/=K .Exps

// Rules for convertStmt function (MethodDeclStmt)
rule convertStmt(T:Type F:Id ( Ps:Parameters ) B:Block, M:Map) =>
    "method " +String Id2String(F) +String "( " +String
    convertParameters(Ps) +String ")" +String
    #if T ==K void 
    #then "" 
    #else " returns ( RES__: " +String convertType(T) +String " )"
    #fi
    +String "\n\tdecreases *\n\tmodifies this"
    +String convertStmt(B, M)

rule convertStmt(C:Id ( Ps:Parameters ) B:Block, M:Map) =>
    "constructor CONSTRUCTOR_" +String Int2String(#length(Ps)) +String 
    "_PARAM( " +String convertParameters(Ps) +String ")" +String
    "\n\tdecreases *" +String "\n{\n//Default Member Variable Values Here\n" 
    +String {M[C]}:>String +String convertStmt(B, M) +String "}\n"

rule convertStmt(Ms:Modifiers S:MethodDeclStmt, M:Map) 
    => convertModifiers(Ms) +String convertStmt(S, M)

// Rules for convertStmt and convertClassDeclStmt functions
rule convertStmt(_:Modifiers S:ClassDeclStmt, M:Map) 
    => convertClassDeclStmt(S, M)

rule convertClassDeclStmt(_:Modifiers S:VarDeclStmt, M:Map) 
    => convertClassDeclStmt(S, M)

rule convertClassDeclStmt(_:Type .Exps ;, _:Map) => ""

rule convertClassDeclStmt(T:Type X:Id ;, _:Map) => 
    "var " +String Id2String(X) +String ": " +String convertType(T) +String "\n"

rule convertClassDeclStmt(T:Type X:Id = _:Exp ;, _:Map) => 
    "var " +String Id2String(X) +String ": " +String convertType(T) +String "\n"

rule convertClassDeclStmt(T:Type E:Exp , Es:Exps ;, M:Map) => 
    convertClassDeclStmt(T E ;, M) +String convertClassDeclStmt(T Es ;, M)
    requires Es =/=K .Exps

rule convertClassDeclStmt(class C:Id B:Block, M:Map) =>
    "class " +String Id2String(C) +String convertClassDeclStmt(B, M)

rule convertClassDeclStmt(interface I:Id B:Block, M:Map) =>
    "trait " +String Id2String(I) +String convertClassDeclStmt(B, M)

rule convertClassDeclStmt(interface I:Id extends I0:Id B:Block, M:Map) =>
    "trait " +String Id2String(I) +String " extends " +String
    Id2String(I0) +String convertClassDeclStmt(B, M)

rule convertClassDeclStmt(class C:Id implements Is:Ids B:Block, M:Map) =>
    "class " +String Id2String(C) +String " extends " +String
    convertIds(Is) +String convertClassDeclStmt(B, M)

rule convertClassDeclStmt(_:Modifiers S:VarDeclStmt, M:Map) 
    => convertClassDeclStmt(S, M)

rule convertClassDeclStmt(Ms:Modifiers S:MethodDeclStmt, M:Map) 
    => convertModifiers(Ms) +String convertStmt(S, M)

rule convertClassDeclStmt({ S:Stmt }, M:Map) => 
    "\n{\n" +String convertClassDeclStmt(S, M) +String "}\n"
    
rule convertClassDeclStmt({ }, _:Map) => "\n{}\n"

rule convertClassDeclStmt(S1:Stmt S2:Stmt, M:Map) => 
    convertClassDeclStmt(S1, M) +String convertClassDeclStmt(S2, M)

// Rules for convertStmt function (IfStmt)
rule convertStmt(if (E:Exp) B1:Block else B2:Block, M:Map) =>
    "if(" +String convertExp(E) +String ")" +String convertStmt(B1, M)
    +String "else" +String convertStmt(B2, M)

rule convertStmt(if (E:Exp) B:Block, M:Map) =>
    "if(" +String convertExp(E) +String ")" +String convertStmt(B, M)

rule convertStmt(if (E:Exp) B1:Block else if (E2:Exp) B2:Block, M:Map) =>
    "if(" +String convertExp(E) +String ")" +String convertStmt(B1, M) +String 
    "else if(" +String convertExp(E2) +String ")" +String convertStmt(B2, M)

rule convertStmt(if (E:Exp) B1:Block else S:IfStmt, M:Map) =>
    "if(" +String convertExp(E) +String ")" +String convertStmt(B1, M) +String 
    "else " +String convertStmt(S, M)

// Rules for convertStmt function (WhileStmt)
rule convertStmt(while (E:Exp) B:Block, M:Map) =>
    "while(" +String convertExp(E) +String ")" +String "\n"
    +String "decreases *" +String convertStmt(B, M)

// Rules for ForStmt
// `for` loops will be converted to `while` loops, since Dafny does not 
// offer good support on `for` loops
rule #expsToStmt(.Exps) => ;
rule #expsToStmt(E:Exp) => E;
rule #expsToStmt(E1:Exp, E2:Exp, Es:Exps) => E1; E2; #expsToStmt(Es)

rule for(Init:Stmt Condition:Exp ; Steps:Exps) LoopBody:Block =>
        { 
            Init boolean String2Id("ExecSteps__") = false; 
            while (Condition)
            {
                if(String2Id("ExecSteps__") == false) 
                {
                    String2Id("ExecSteps__") = true;
                }
                else
                {
                    #expsToStmt(Steps)
                }
                LoopBody
            } 
        }

rule for(Init:Stmt ; Steps:Exps) LoopBody:Block =>
        { 
            Init boolean String2Id("ExecSteps__") = false; 
            while (true)
            {
                if(String2Id("ExecSteps__") == false) 
                {
                    String2Id("ExecSteps__") = true;
                }
                else
                {
                    #expsToStmt(Steps)
                }
                LoopBody
            } 
        }

// Rules for convertStmt function (other statements)
rule convertStmt(E:Exp ;, _:Map) => convertExp(E) +String ";\n"

rule convertStmt(return E:Exp ;, _:Map) 
    => "return " +String convertExp(E) +String ";\n"
rule convertStmt(return ;, _:Map) => "return ;\n"

rule convertStmt(continue ;, _:Map) => "continue;\n"

rule convertStmt(break ;, _:Map) => "break;\n"

rule convertStmt(;, _:Map) => "\n"

rule convertStmt(S1:Stmt S2:Stmt, M:Map) 
    => convertStmt(S1, M) +String convertStmt(S2, M)

rule convertStmt(System.out.println(E:Exp) ;, _:Map)
    => "print( " +String convertExp(E) +String " );\nprint(\"\\n\");\n"

endmodule
