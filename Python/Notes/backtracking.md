# Backtracking

A backtracking algorithm is a problem-solving algorithm that uses a brute force approach for finding a desired output.

Three types of problems in backtracking:
- Decision problem - search for a feasible solution
- Optimization problem - search for the best solution
- Enumeration problem - find all feasible solutions

Three steps in bakctracking:
1. Backtracking checks whether the given node is a valid solution or not.
2. Discard several invalid solutions with one iteration.
3. Enumerate all subtree of the node to find the valid solution.

## Backtracking vs Brute force
Backtracking is usually a little faster because it can eliminate multiple bad solutions in one iteration.

## N Queens Problem
Place N queens in NxN board, so that no queen is being attacked by another.
