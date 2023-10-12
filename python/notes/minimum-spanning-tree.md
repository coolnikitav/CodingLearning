# Minimum Spanning Tree (Disjoing set)

A minimum spanning tree (mst) is a subset of the edges of connected, weighted and undirected graph which:
- Connects all vertices together
- No cycle
- Minimum total edge

# Disjoint set

It is a data structure that keeps track of set of elements which are partitioned into a number of disjoint and non overlapping sets and each sets have representative which helps in identifying that sets.
- Make set
- Union
- Find set

## Operations:
makeSet(N): used to create an initial set
union(x, y): merge two given sets

Time complexity: O(log N)
Space complexity: O(n)
