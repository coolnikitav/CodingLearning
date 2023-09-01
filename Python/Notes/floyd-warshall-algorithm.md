# Floyd Warshall Algorithm

If D[u][v] > D[u][viaX] + D[viaX][v]:
  D[u][v] = D[u][viaX] + D[viaX][v]

Does not work with negative cycles.

Time complexity: O(V^3)

Space complexity: O(V^2)
