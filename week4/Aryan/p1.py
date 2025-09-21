from z3 import *
from functools import reduce

# There are exactly 13 moves in a perfect game:
# 1 initial move + 6 full rounds (2 moves each)
moves = [Int(f"move_{i}") for i in range(13)]

constraints = []

# Each move must be between 1 and 3
for move in moves:
    constraints.append(And(move >= 1, move <= 3))

# Total of all moves must equal 21
constraints.append(Sum(moves) == 21)

# --- Winning Strategy Constraints ---

# 1. Player 1 starts by taking exactly 1
constraints.append(moves[0] == 1)

# 2. From round 2 onward, Player 1's move + Player 2's move <= 4
#    (to handle last round when fewer than 4 stones remain)
for i in range(2, 13, 2):  # even indices >= 2
    constraints.append(moves[i] + moves[i - 1] <= 4)

# 3. Ensure Player 1 makes the last move
last_move_indices = [If(moves[i] > 0, i, -1) for i in range(13)]

def z3_max(a, b):
    return If(a > b, a, b)

max_index = reduce(z3_max, last_move_indices)
constraints.append(max_index % 2 == 0)  # even index => Player 1

# --- Solve ---
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    sequence = [model[moves[i]].as_long() for i in range(13) if model[moves[i]].as_long() > 0]
    print("Optimal winning sequence for Player 1:", sequence)
else:
    print("No winning strategy found.")
