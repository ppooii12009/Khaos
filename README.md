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

### 2. Static Verification with Dafny

This repository also supports static code verification using [Dafny](https://dafny.org/). You can find the steps and guidance for static verification in the relevant directories or documentation within this repository.

## Contribution

Contributions and suggestions are welcome! Please feel free to submit issues and pull requests to help improve the code.

## Contact

If you have any questions or feedback, please contact us at [your-email@example.com](mailto:your-email@example.com).

---

Be sure to replace `<repository-url>` and `<repository-name>` with your actual repository link and name to ensure users can clone and use your repository seamlessly. Adjust or supplement other specific information according to your needs.
