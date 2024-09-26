requires "type.k"
requires "exp.k"
requires "stmt.k"

module JAVA-SYNTAX
    imports TYPE-SYNTAX
    imports EXP-SYNTAX
    imports STMT-SYNTAX
    imports DOMAINS-SYNTAX

syntax KItem ::= openLogFile()
                | closeLogFile()
                | writeToLog(String)
                | beginAnalyze()
                | beginConvert()
                | setCurrentClass(Id)

syntax Id ::= "Object"                      [token]

endmodule

module JAVA
    imports JAVA-SYNTAX
    imports TYPE
    imports EXP
    imports STMT
    imports DOMAINS
    imports K-IO

    configuration <T color="red">
                    <k color="green"> 
                        openLogFile()
                        ~> writeToLog("newtype int8 = x | -0x80 <= x < 0x80\n")
                        ~> writeToLog("newtype int16 = x: int | -128 <= x < 128\n")
                        ~> writeToLog("newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000\n")
                        ~> writeToLog("newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000\n")
                        ~> beginAnalyze()
                        ~> beginConvert()
                        ~> closeLogFile() 
                    </k>
                    <logFile> 0 </logFile>
                    <copy> $PGM:Stmt </copy>
                    <currentClass> Object </currentClass>
                    <extraAssignment> .Map </extraAssignment>
                    <statusCode> 1 </statusCode>
                    <analyzing> true </analyzing>
                    <test> "" </test>
                </T>

rule    <k> openLogFile() => .K ... </k>
        <logFile> _ => {#open("result.dfy","w+")}:>Int </logFile>

rule    <k> closeLogFile() => #close(FD) ... </k>
        <logFile> FD:Int </logFile>

rule    <k> writeToLog(Content:String) => #write(FD, Content) ... </k>
        <logFile> FD:Int </logFile>

rule    <k> .K </k>
        <statusCode> 1 => 0 </statusCode>

rule    <k> beginAnalyze() => S ... </k>
        <copy> S:Stmt </copy>
        <analyzing> _ => true </analyzing>

rule    <k> beginConvert() => S ... </k>
        <copy> S:Stmt </copy>
        <analyzing> _ => false </analyzing>

rule    <k> S:Stmt => writeToLog(convertStmt(S, M)) ... </k>
        //<k> S:Stmt => .K ... </k>
        //<test> T => T +String convertStmt(S, M) </test>
        <extraAssignment> M:Map </extraAssignment>
        <analyzing> false </analyzing>

// rules for analyzing classes
rule    <k> setCurrentClass(C:Id) => .K ... </k>
        <currentClass> _ => C </currentClass>
        <extraAssignment> ... .Map => C |-> "" ... </extraAssignment>
        <analyzing> true </analyzing>

rule    <k> _:Modifiers S:ClassDeclStmt => S ... </k>
        <analyzing> true </analyzing>

rule    <k> { } => .K ... </k>
        <analyzing> true </analyzing>

rule    <k> { S:Stmt } => S ... </k>
        <analyzing> true </analyzing>

rule    <k> class C:Id B:Block => setCurrentClass(C) ~> B ... </k>
        <analyzing> true </analyzing>

rule    <k> interface I:Id B:Block => setCurrentClass(I) ~> B ... </k>
        <analyzing> true </analyzing>

rule    <k> 
            interface I:Id extends _:Id B:Block 
                => setCurrentClass(I) ~> B ...
        </k>
        <analyzing> true </analyzing>

rule    <k> 
            class C:Id implements _:Ids B:Block
                => setCurrentClass(C) ~> B ...
        </k>
        <analyzing> true </analyzing>

rule    <k> _:Modifiers S:VarDeclStmt => S ... </k>
        <analyzing> true </analyzing>

rule    <k> _:Type .Exps ; => .K ... </k>
        <analyzing> true </analyzing>

rule    <k> _:Type _:Id ; => .K ... </k>
        <analyzing> true </analyzing>

rule    <k> _:Type X:Id = E:Exp ; => .K ... </k>
        <currentClass> C </currentClass>
        <extraAssignment> 
            ... 
                C |-> (Old:String 
                    => Old +String "this." +String Id2String(X) +String
                    " := " +String convertExp(E) +String " ;\n") 
            ... 
        </extraAssignment>
        <analyzing> true </analyzing>

rule    <k> T:Type E:Exp , Es:Exps ; => T E ; T Es ; ... </k>
        <analyzing> true </analyzing>
        requires Es =/=K .Exps

rule    <k> _:Modifiers _:MethodDeclStmt => .K ... </k>
        <analyzing> true </analyzing>

rule    <k> _:MethodDeclStmt ; => .K ... </k>
        <analyzing> true </analyzing>

endmodule