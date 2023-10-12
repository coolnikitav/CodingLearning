# What is single source shortest path?
A single source problem is about finding a path between a given vertex (called source) to all other vertices in a graph such that the total distance between them (source and destination) is minimum.

# What is all pair shortest path problem?
All pair shortest path problem is about finding a path between every vertex to all other vertices in a graph such that the total distance between them (source and destination) is minimum.

# Which algorithm to use?
|  | BFS | Dijkstra | Bellman Ford | Floyd Warshall |
| :--- | :---: | :---: | :---: | :---: |
| Time Complexity | O(V^3) | O(V^3) | O(EV^2) | O(V^3) |
| Space Complexity | O(EV) | O(EV) | O(V^2) | O(V^2) |
| Implementation | Easy | Moderate | Moderate | Moderate |
| Limitation | Doesn't work for <br> weighted graph | Doesn't work for <br> negative cycles | N/A | Doesn't work for <br> negative cycle |
| Unweighted graph | **Use this as time complexity <br> is good and easy to implement** | Don't use as priority <br> queue slows it | Don't use as time complexity <br> is bad | **Can be used** |
| Weighted graph | Not supported | **Can be used** | Don't use as time complexity <br> is bad | **Can be preferred as <br> implementation is easy |
| Negative cycle | Not supported | Not supported | **Use this** | Not supported
