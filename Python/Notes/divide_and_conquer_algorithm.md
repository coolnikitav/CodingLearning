# Divide and Conquer Algorithm
Divide and conquer algorithm design paradigm which works by recursively breaking down a problem into subproblems of similar type, until these become simple enough to be solved
directly. The solutions to the subproblems are then combined to give a solution to the original problem.

### Optimal substructure
If any problem's overall optimal solution can be constructed from the optimal solutions of its subproblem then this problem has optimal substructure

### Why do we need it?
It is very effective when the problem ahs optimal substructure property.

## Common Divide and Conquer algorithms
- Merge sort
- Quick sort

## Number Factor
Problem statement:
- Given N, find the number of ways to express N as a sum of 1, 3, and 4.

Example:
- N = 4
- Number of ways = 4 : {4}, {1,3}, {3,1}, {1,1,1,1}

## House Robber
Problem statement:
- Given N number of houses along the street with some amount of money
- Adjacent houses cannot be stolen
- Fidn the maximum amount that can be stolen

# Convert String
Problem statement:
- S1 and S2 are given strings
- Convert S2 to S1 using delete, insert, or replace operations
- Find the minimum count of edit operations

# Zero One Knapsack Problem

Problem statement:
- Given the weights and profits of N items
- Find the maximum profit within given capacity of C
- Items cannot be broken