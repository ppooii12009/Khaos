/**
    This file defines the configuration and 
 */
module CONFIGURATION-SYNTAX
    imports DOMAINS-SYNTAX
    imports STMT-SYNTAX

/** 
    Syntax declaration for program execution and termination markers
 */
syntax KItem ::= "__execute__"
syntax KItem ::= "__exit__"

/**
    Syntax declaration runtime error operation
    Params:
        - String: Error message for runtime errors
 */
syntax KItem ::= runtimeError(String)       
/**
    Syntax declaration for stopping the program
 */
                | stuck() 
/**
    Syntax declaration for adding pre-defined built-in classes
    Params:
        - Int: The index of pre-defined class
 */
                | addBuildinClass(Int)
/**
    Syntax declaration for opening log file
 */
                | openLogFile()
/**
    Syntax declaration for closing log file
 */
                | closeLogFile()

endmodule

module CONFIGURATION
    imports CONFIGURATION-SYNTAX
    imports DOMAINS
    imports STMT
    imports K-IO

// Configuration
// the syntax declarations below are required because the sorts are
// referenced directly by a production and, because of the way KIL to KORE
// is implemented, the configuration syntax is not available yet
// should simply work once KIL is removed completely
// check other definitions for this hack as well
syntax EnvCell
syntax ControlCellFragment
syntax MemberStackCell
syntax CrntObjCellFragment

configuration <T color="red">
                    <threads color="orange">
                        // Simulate thread
                        <thread multiplicity="*" type="Set" color="yellow" initial="">
                            // Program waited to be execute
                            <k color="green"> 
                                openLogFile()
                                ~>
                                ($PGM:Stmt ~> addBuildinClass(1) ~> __execute__) 
                            </k>
                            // Control flow information
                            <control color="cyan">
                                // Handle the program context when calling and returning from functions
                                <fstack color="blue"> .List </fstack>
                                // Handle the program context when entering and exiting from loops
                                <lstack color="LemonChiffon"> .List </lstack>
                                // Mark whether the current program is in a global function or inside an instance object
                                <estack color="Periwinkle"> ListItem(.Map) </estack>
                                // The return value type of the currently executing function
                                <returnType color="LimeGreen"> void:Type </returnType>
                                // The object instance currently being constructed
                                <crntObj color="Fuchsia">
                                    // The class/type of current object instance
                                    <crntClass> Object </crntClass>
                                    // Member variables and functions (including those of its all parent classes)
                                    <memberStack> .List </memberStack>
                                    // The pre-allocated address for storing its members
                                    <location multiplicity="?"> .K </location>
                                </crntObj>
                            </control>
                            // The variable environment currently accessible
                            <env color="violet"> .Map </env>
                            // Thread id
                            <id color="pink"> 0 </id>
                            // Whether the program has entered the `main()` function
                            <isGlobal color="blue"> true </isGlobal>
                            // Whether program specification checking needs to be skipped
                            //     @ Note: This attribute is used to avoid infinite recursive checking.
                            <skipCheck color="red"> false </skipCheck>
                            // Whether to prohibit ordinary permissions from printing content to the console
                            //     @ Note: The information about program specification checking will still be printed. 
                            //     If you don't want to print it, you can modify the rewrite rules of 
                            //     `forceprint()/forceprintln()` yourself.
                            <skipPrint color="yellow"> false </skipPrint>
                            // Flag indicating whether the thread is newly created
                            // Used to maintain `<schedule>`
                            <new color="white"> true </new>
                        </thread>
                    </threads>
                    // Schedule threads
                    <schedule>
                        // The set of running thread IDs
                        <running> SetItem(0):Set </running>
                        // Locked memory
                        <lock color="cyan"> .Set </lock>
                        // The set of terminated thread IDs
                        <terminated color="red"> .Set </terminated>
                        // The set of all schedulable thread IDs
                        <ready color="blue"> SetItem(0):Set </ready>
                        // The set of all suspended thread IDs
                        <suspended color="yellow"> .Set </suspended>
                        // Seed used for random algorithm
                        <seed> $SEED:Int </seed>
                        // Counter for regularly scheduling threads
                        <counter> 0 </counter>
                        // Counter for detecting deadlock
                        <deadCounter> 0 </deadCounter>
                        // Maximum value of `deadCounter`
                        <maxDeadCounter> 0 </maxDeadCounter>
                        // Whether the CPU is occupied by some threads
                        // @ `true` to prohibit thread scheduling
                        // @ `false` to allow thread scheduling
                        <occupied> false </occupied>
                    </schedule>
                    // The memory space
                    // The key-value pairs exist in the form of `Int |-> KItem`, 
                    // where the left side represents the memory address (an integer) 
                    // and the right side represents the content stored in that space.
                    <store color="white"> .Map </store>
                    // The next available address to allocate
                    <nextAddress color="green"> 0 </nextAddress>
                    // Global function definitions
                    // The data storage format is: `Id |-> (Types |-> Function)`
                    // The outer key (an Id) represents the function name, and the value 
                    // corresponding to this key is still a map, which contains several 
                    // key-value pairs in the form of `Types |-> Function`, representing several 
                    // overloaded functions with the same name but different parameter types.
                    <gFunctions color="pink"> .Map </gFunctions>
                    // Global variable references
                    <gVariables color="white"> .Map </gVariables>
                    // Input stream
                    <input color="magenta" stream="stdin"> .List </input>
                    // Output stream
                    <output color="brown" stream="stdout"> .List </output>
                    // Class information
                    <classes color="Fuchsia">
                        // Class data of a single class
                        <classData multiplicity="*" type="Map" color="Fuchsia">
                            // Class name
                            <className color="Fuchsia"> Object </className>
                            // Its direct parent class
                            <baseClass color="Fuchsia"> Object </baseClass>
                            // Member variables and functions definition
                            <declarations color="Fuchsia"> .K </declarations>
                        </classData>
                    </classes>
                    // Store the direct parent class information corresponding to each class
                    <inheritanceMap color="Fuchsia"> .Map </inheritanceMap>
                    // Program status code
                    //     @ `0` for terminated successfully
                    //     @ `1` for not terminated or an error has occurred
                    <statusCode exit=""> 1 </statusCode>
                    // Error message
                    <errorMessage color="red"> "" </errorMessage>
                    // Log file descriptor
                    <logFile> 0 </logFile>
                </T>

// Top-level processing is complete, entering the `main()` function
rule    <k> __execute__ => main(.Exps); ... </k> 
        <env> Env </env>
        <gVariables> _ => Env </gVariables>
        <isGlobal> _ => false </isGlobal>

// No more pre-defined classes need to be added
rule    <k> addBuildinClass(_:Int) => .K ... </k>
        [owise]

// Runtime error detected, program stuck
rule    <k> runtimeError(Message:String) => stuck() ... </k>
        <errorMessage> EM => EM +String " [ " +String Message +String " ] " </errorMessage>

// Log file operations
rule    <k> openLogFile() => .K ... </k>
        <logFile> _ => {#open("output","w+")}:>Int </logFile>

rule    <k> closeLogFile() => #close(FD) ... </k>
        <logFile> FD:Int </logFile>

endmodule