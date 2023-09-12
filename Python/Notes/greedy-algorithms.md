# Greedy Algorithms

- It is an algorithmic paradigm that builds the solution piece by piece
- In each step it chooses the piece that offers most obvious and immediate benefit
- It fits perfectly for those solutions in which local optimal solutions lead to global solution

### Greedy algorithm examples:
- Insertion sort
- Selection sort
- Topological sort
- Prim's algorithm
- Kruskal algorithm

### Problems solved with greedy algorithms:
- Activity selection problem
- Coin change problem
- Fractional knapsack problem

## Activity Selection problem
Given N number of activities with their start and end times. We need to select the maximum number of activities
that can be performed by a single person, assuming that a person can only work on a single activity at a time.

Algorithm:
- Sort activities based on finish time
- Select first activity from sorted array and print it
- For all remaining activities:
    - If the start time of this activity is greater or equal to the finish time of previously selected activity then select this activity and print it

Time complexity: O(NlogN)

Space complexity: O(1)

## Coin change problem
You are given coins of different denominations and total amount of money. Find the minimum number of coins that you need to make up the given amount.

Algorithm:
- Find the biggest coin that is less than given total number
- Add coin to the result and subtract coin from total number
- Repeat until its zero

Time complexity: O(N)

Space complexity: O(1)

## Fractional Knapsack Problem
Given a set of items, each with a weight and a value, determine the number of each item to include in a collection so that the total weight is less than or equal to a given limit and the total value is a large as possible.

Algorithm:
- Calculate the density or ratio for each item
- Sort items based on this ratio
- Take items with the highest ratio sequentially until weight allows
- Add the next item as much (fractional) as we can

Time complexity: O(NlogN)

Space compleixty: O(1)