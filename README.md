# Khaos
This repository contains the code implementation for the paper titled [Khaos: A K Framework-based Approach to Simulation and Verification]. 
The implementation offers two primary functions: dynamic execution and static code verification using Dafny.

## Prerequisites

Before proceeding, make sure you have the [K Framework](https://github.com/runtimeverification/k) installed on your system. Follow the instructions in the repository to set it up.

## Features

### 1. Dynamic Execution

You can perform dynamic execution with the following steps:

1. Clone this repository to your local machine:
   ```bash
   git clone https://github.com/ppooii12009/Khaos.git
   cd Khaos
   ```

2. Compile the `language.k` file:
   ```bash
   kompile language.k
   ```

3. Run the following command to execute codes in `MES` file dynamically:
   ```bash
   krun MES -cSEED=99 --output-file output.txt
   ```

   - `-cSEED=99`: Sets the random seed to 99.
   - `--output-file output.txt`: Outputs the result to the file `output.txt`.
  
   After executing the commands, you can view the program's configuration details in the `output.txt` file located in the current directory.

### 2. Static Verification with Dafny

This repository supports static code verification by converting the relevant code to equivalent Dafny code using the K Framework, followed by manual verification with Dafny. Follow these steps to perform static verification:

1. Navigate to the `Khaos/lib/converter` directory:
   ```bash
   cd Khaos/lib/converter
   ```

2. Compile the `java.k` file:
   ```bash
   kompile java.k
   ```

3. Execute the conversion:
   ```bash
   krun program
   ```

After converting, you can manually use Dafny to verify the generated Dafny code in `result.dfy` file.

---
