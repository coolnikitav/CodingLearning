class Solution(object):
    def minReorder(self, n, connections):
        """
        :type n: int
        :type connections: List[List[int]]
        :rtype: int
        """

        # Create a graph with bidirectional edges
        self.graph = {key: [] for key in range(n)}

        for edge in connections:
            self.add_edge(edge[0], edge[1])

        # Traverse the graph with DFS from 0
        # If the edge is not in connections, then that path needs to be changed
        reorder_count = 0

        visited_cities = {0}
        city_stack = [0]

        while city_stack:
            current_city = city_stack.pop()

            if current_city not in visited_cities:
                visited_cities.add(current_city)
            
            for city in self.graph[current_city]:
                if city not in visited_cities:
                    city_stack.append(city)

                    if [city, current_city] not in connections:
                        reorder_count += 1

        return reorder_count


    def add_edge(self, vertex1, vertex2):
        if vertex1 in self.graph.keys() and vertex2 in self.graph.keys():
            self.graph[vertex1].append(vertex2)
            self.graph[vertex2].append(vertex1)

solution = Solution()
connections = [[0,2],[0,3],[4,1],[4,5],[5,0]]
print(solution.minReorder(len(connections)+1, connections))