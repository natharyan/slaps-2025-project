# Week 1: Setup and Environment Installation

## Overview
This week focuses on setting up your development environment and familiarizing yourself with the tools needed for the invariant synthesis project.

## Deliverables
1. **Environment Setup**: Install Dafny, Z3, and related tools
2. **Repository Creation**: Create a GitHub repository and give access to course instructor and teaching assistant
3. **Tool Testing**: Test Dafny on 3 example programs to familiarize yourself with the workflow
4. **Submission**: Repository link and test results

## Installation Guide

### Required Tools

#### 1. Dafny Installation
Dafny is Microsoft's verification-aware programming language.

**Resources:**
- **Official Documentation**: [https://dafny.org](https://dafny.org)
- **Installation Guide**: Follow the official installation instructions for your platform
- **IDE Integration**: Consider using VS Code with the Dafny extension
- **Textbook**: [Program Proofs](https://mitpress.mit.edu/9780262046402/program-proofs/) by K. Rustan M. Leino

#### 2. Z3 Theorem Prover
Z3 is Microsoft's theorem prover that Dafny uses.

**Resources:**
- **Official Repository**: [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3)
- **Documentation**: [https://github.com/Z3Prover/z3/wiki](https://github.com/Z3Prover/z3/wiki)
- **Textbook**: [The Calculus of Computation](https://link.springer.com/book/10.1007/978-3-540-74113-8) by Bradley and Manna
- **Python Package**: `pip install z3-solver`
- **Other Languages**: Follow platform-specific installation guides

#### 3. Programming Language Setup
Choose your preferred language for implementing the synthesis tool:

**Python (Recommended):**
- Install Python 3.8+
- Install required packages: `z3-solver`, `ply` (for parsing)

**OCaml (Alternative):**
- Install OCaml and opam
- Install required packages: `z3`, `menhir` (parser generator)

#### 4. Version Control
- Install and configure Git
- Set up your GitHub repository
- Configure proper `.gitignore` for your chosen language

### Verification
After installation, verify that both Dafny and Z3 are working correctly:

1. **Test Dafny**: Create a simple Dafny program and verify it
2. **Test Z3**: Create a simple constraint satisfaction problem
3. **Test Integration**: Ensure Dafny can find and use Z3

Refer to the official documentation for specific verification examples.

## Tasks

### 1. Environment Setup
- Follow the installation instructions above
- Install Dafny following the official documentation at [https://dafny.org](https://dafny.org)
- Install Z3 for your chosen programming language
- Set up your preferred development environment (VS Code recommended)

### 2. Repository Setup
- Create a new GitHub repository for your project
- Add course instructor and teaching assistant as collaborators
- Clone the repository to your local machine
- Set up proper `.gitignore` file

### 3. Tool Testing
Test Dafny with the following example programs:
- `examples/example1.dfy` - Sum of natural numbers
- `examples/example2.dfy` - Factorial calculation
- `examples/example3.dfy` - Fibonacci calculation

### 4. Verification Steps
For each example:
1. Run `dafny verify filename.dfy`
2. Ensure verification passes
3. Try modifying the programs and observe how verification behaves
4. Document any issues encountered and their solutions

## Getting Help
- **Dafny documentation**: https://dafny.org/
- **Z3 documentation**: https://github.com/Z3Prover/z3/wiki
- **Course instructor office hours**
- **Teaching assistant support**
- **Dafny Zulip channel** (linked from dafny.org)

## Next Steps
After completing Week 1:
- Review loop invariant concepts for Week 2
- Familiarize yourself with Dafny syntax and features
- Set up your development workflow
