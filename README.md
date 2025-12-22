# Khaos
This repository contains the code implementation for the paper titled [Towards Integrated Formal Methods: Khaos, A LaaS-FaaS based Solution]. 
The implementation offers a proof-of-concept of the proposed solution in the paper. Test codes are also included.

<img width="803" height="458" alt="image" src="https://github.com/user-attachments/assets/440a11d2-8ef6-434f-8107-9d1f33176450" />

## Prerequisites

Before proceeding, make sure you have the [K Framework](https://github.com/runtimeverification/k) installed on your system. Follow the instructions in the repository to set it up.
Also, we recommend to install [Dafny](https://dafny.org/latest/Installation) for running the generated Dafny codes.

## How To Run PoC Test Codes

### 1. Positive Test Codes 

#### You can perform the positive test with the following steps:

1. Clone this repository to your local machine:
   ```bash
   git clone https://github.com/ppooii12009/Khaos.git
   cd Khaos
   ```

2. Compile the `language.k` file:
   ```bash
   kompile language.k
   ```

3. Run the following command to execute codes in `Positive_MES` file dynamically:
   ```bash
   krun Positive_MES -cSEED=99 --output-file output.txt
   ```

   - `-cSEED=99`: Sets the random seed to 99.
   - `--output-file output.txt`: Outputs the result to the file `output.txt`.
  
   After executing the commands, you can view the program's configuration details in the `output.txt` file located in the current directory.

4. Run the codes in `Positive_MES.java` in your installed JAVA IDE. Compare the output result with the result in Step 3.

#### For code transformation mechanism test, follow the steps below:

1. Clone this repository to your local machine:
   ```bash
   git clone https://github.com/ppooii12009/Khaos.git
   cd Khaos/lib/converter
   ```

2. Compile the `java.k` file:
   ```bash
   kompile java.k
   ```
   
3. Run the following command to transform JAVA codes to Dafny codes in `program` file:
   ```bash
   krun program
   ```
  
   After executing the commands, you can find the generated file `result.dfy` in current directory.

### 2. Negative Test Codes

You can perform the negative test with the following steps:

1. Clone this repository to your local machine:
   ```bash
   git clone https://github.com/ppooii12009/Khaos.git
   cd Khaos
   ```

2. Compile the `language.k` file:
   ```bash
   kompile language.k
   ```

3. Run the following command to execute codes in `Negative_MES` file:
   ```bash
   krun Negative_MES -cSEED=99 --output-file output.txt
   ```

   After the execution, check the console output in `output.txt` and find the value of conflict count.

4. Run the codes in `Negative_MES.java` in your installed JAVA IDE. Check the console output and compare them with the result in Step 3.

---
