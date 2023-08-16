# Graph traversal

### Breadth first search (BFS):
- Look at the dictionary structure. Start at vertex, go through all of its edges in order. If you have already visited an edge, move to the next one.

Time complexity: O(V+E)

Space complexity: O(V)

When to use:
- If we know that the target is close to the starting point.

### Depth first search (DFS):
- Go to the deepest node for each node.

Time complexity: O(V+E)

Space complexity: O(V)

When to use:
- If we already know that the target vertex is buried very deep.