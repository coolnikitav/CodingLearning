# Single Source Shortest Path Problem (SSSPP)

A single source problem is about finding a path between a given vertex (called source) to all other vertices in a graph such that the total distance between them (source and destination) is minimum.

## Methods:
### BFS
- Time complexity: O(E)
- Space complexity: O(E)
- It is not V+E because we are only visiting connected verteces. If a vertex is isolated, we will not visit it.
- BFS does not work with weighted graphs
### Dijkstra's algorithm
### Bellman Ford