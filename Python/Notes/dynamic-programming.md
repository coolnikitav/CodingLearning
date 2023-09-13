# What is dynamic programming?
Dynamic programming(DP) is an algorithmic technique for solving an optimization problem by
breaking it down into simpler subproblems and utilizing the fact that the optimal solution to the overall 
problem depends upon the optimal solution to its subproblems.

### Optimal substructure:
If any problem's overall optimal solution can be constructed from the optimal solutions of its subproblem then this problem has optimal substructure.

Example: Fib(n) = Fib(n-1) + Fib(n-2)

### Overlapping subproblem:
Subproblems are smaller versions of the original problem. Any problem has overlapping sub-problems if finding its solution involves solving the same subproblem multiple times.

## Approaches

### Top Down with Memoization
Solve the bigger problem by recursively finding the solution to smaller subproblems. Whenever we solve a sub-problem, we cache its result so that we don't end up solving
it repeatedly if it's called multiple times. This technique of storing the results of already solved subproblems is called Memoization.

Regular fibonacci:
```
Fibonacci(n):
  If n = 1 return 0
  If n = 2 return 1
  Else
    return Fibonacci(n-1) + Fibonacci(n-2)
```
Time complexity: O(c^n)

Space complexity: O(n)

DP fibonacci:
```
Fibonacci(n):
  if n = 1 return 0
  if n = 2 return 1
  if not in memo:
    memo[n] = Fibonacci(n-1, memo) + Fibonacci(n-2, memo)
  return memo[n]
```
Time complexity: O(n)

Space complexity: O(n)
