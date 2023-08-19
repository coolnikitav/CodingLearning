# Single Source Shortest Path Problem (SSSPP)

A single source problem is about finding a path between a given vertex (called source) to all other vertices in a graph such that the total distance between them (source and destination) is minimum.

## Methods:
### BFS
- Time complexity: O(E)
- Space complexity: O(E)
- It is not V+E because we are only visiting connected verteces. If a vertex is isolated, we will not visit it.
- BFS does not work with weighted graphs
### Dijkstra's algorithm
- Dijkstra's algorithm to find the shortest path between a and b. It picks the unvisited vertex with the lowest distance, calculates the distance through it to each unvisited neighbor, and updates the neighbor's distance if smaller.
- Does not work with negative cycles.
### Bellman Ford
- Same as Dijkstra's algorithm, but reports if there is a negative cycle.
- Runs V-1 times:
    - If any node is achieved better distance in previous iteration, then that better distance is used to improve distance of other vertices
    - Identify worst case graph that can be given to us (A->B->C->D->E for 5 node graph)