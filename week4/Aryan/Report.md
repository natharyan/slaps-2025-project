# Output:

Optimal winning sequence for Player 1: [1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1]

- Z3 looks for numbers that satisfy all these rules at once.
- The solution it finds is optimal because of the constraint on the number of rounds and the sum after each round is <= 4.

# TODO:
- For later look into z3 minimize.