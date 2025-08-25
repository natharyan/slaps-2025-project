# Week 2: Manual Loop Invariant Writing

## Overview
This week focuses on writing loop invariants by hand for given problems. This exercise will help you understand the fundamentals of loop invariants and prepare you for automated synthesis.

## Deliverables
1. **Solutions**: Complete Dafny programs with your handwritten invariants for 5 given problems
2. **Explanations**: Detailed explanations of why your invariants are correct
3. **Summary**: A summary of the loop invariant concepts covered in class

## Formal Definition of Correct Loop Invariant

A loop invariant is a predicate that satisfies the following three conditions:

### 1. Initialization (Establishment)
The invariant must be true before the loop begins execution.

### 2. Preservation (Maintenance)
If the invariant is true at the beginning of a loop iteration and the loop condition is true, then after executing the loop body, the invariant must still be true.

### 3. Termination (Usefulness)
When the loop terminates, the invariant together with the negation of the loop condition must imply the desired postcondition.

**Mathematical Formulation:**
- Let `I` be the invariant
- Let `B` be the loop condition
- Let `S` be the loop body
- Let `P` be the precondition
- Let `Q` be the postcondition

Then `I` is a correct loop invariant if:
1. `P ⇒ I` (Initialization)
2. `{I ∧ B} S {I}` (Preservation)
3. `I ∧ ¬B ⇒ Q` (Termination)

## Problems

The problems are provided as separate Dafny files in the `problems/` folder:

- **Problem 1**: `problems/problem1.dfy` - Simple Loop with Two Variables
- **Problem 2**: `problems/problem2.dfy` - Integer Division (Quotient & Remainder)
- **Problem 3**: `problems/problem3.dfy` - GCD Calculation
- **Problem 4**: `problems/problem4.dfy` - Fast Power (Exponentiation by Squaring)
- **Problem 5**: `problems/problem5.dfy` - Reversing a Number

Each problem file contains a complete Dafny method with preconditions, postconditions, and TODO comments indicating where you need to write loop invariants.


## Verification Process
1. Write your invariant
2. Run `dafny verify filename.dfy`
3. If verification fails, analyze the error message
4. Refine your invariant based on the feedback
5. Repeat until verification succeeds

## Evaluation Criteria
- **Correctness**: Invariants must be verified by Dafny
- **Completeness**: All required invariants must be provided
- **Explanation Quality**: Clear reasoning for invariant choices
- **Understanding**: Demonstrated grasp of invariant concepts

## Tips for Writing Invariants
- Start with simple invariants and refine them
- Test your invariants with Dafny verification
- Consider both initialization and preservation
- Think about termination conditions
- Use the examples from Week 1 as reference

## Required Reading: CSUR14 Survey Paper

**Start reading**: `../papers/CSUR14.pdf` - "Loop invariants: analysis, classification, and examples" by Furia, Meyer, and Velder

This comprehensive survey paper provides:
- **Classification of loop invariants** by type and complexity
- **Analysis techniques** for understanding invariant patterns
- **Examples** of various invariant categories
- **Theoretical foundations** for invariant synthesis

This reading will provide essential background for understanding the theoretical foundations of loop invariants and prepare you for the automated synthesis work in later weeks.

## Next Steps
After completing Week 2:
- Begin thinking about benchmark problem creation for Week 3
- Review the synthesis tool requirements for Week 6
- Practice with more complex loop patterns