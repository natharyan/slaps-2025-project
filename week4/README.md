# Week 4: Z3 Problem Solving

## Overview
This week focuses on learning and practicing with the Z3 theorem prover through challenging problems. You will solve complex constraint satisfaction problems including game theory, non-linear constraints, and invariant synthesis to understand advanced constraint solving techniques.

## Deliverables
1. **Z3 Problem Solutions**: Solve 3 challenging problems using Z3
2. **Code and Explanations**: Provide working Z3 code with detailed explanations
3. **Learning Reflection**: Document your understanding of Z3 concepts
4. **Submission**: Complete solutions with explanations

## Required Reading
- **Textbook**: [The Calculus of Computation](https://link.springer.com/book/10.1007/978-3-540-74113-8) by Bradley and Manna
- **Z3 Documentation**: [https://github.com/Z3Prover/z3/wiki](https://github.com/Z3Prover/z3/wiki)

## Problems

### Problem 1: Game of 21 (Nims Game)
**Description**: Model and solve the game of 21, where two players take turns removing 1, 2, or 3 objects from a pile of 21 objects. The player who removes the last object wins.

**Requirements**:
- Model the game state and valid moves
- Find a winning strategy for the first player
- Determine if the first player can always win

### Problem 2: Non-Linear Constraint Solving
**Description**: Solve the following system of non-linear constraints:
- x² + y² = 25
- x + y = 7
- x > 0 and y > 0
- Find all integer solutions

### Problem 3: Invariant Synthesis Practice
**Description**: Given a loop with variables i and sum, where:
- Initially: i = 0, sum = 0
- Loop condition: i < n
- Loop body: sum = sum + i; i = i + 1

Find a linear invariant of the form ax + by + c ≤ 0 that holds throughout the loop execution.

**Requirements**:
- Formulate the problem as Z3 constraints
- Find coefficients a, b, c for the invariant
- Verify that your invariant holds for the loop
- Explain the synthesis process
- Test your invariant with different values of n

**Challenge**: Find multiple different linear invariants and compare their strength.

## Next Steps
After completing Week 4:
- Review how advanced Z3 concepts apply to invariant synthesis
- Prepare for parser implementation in Week 5
- Think about how these techniques can be applied to your benchmark problems
