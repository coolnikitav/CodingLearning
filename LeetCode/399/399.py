class Solution(object):
    def calcEquation(self, equations, values, queries):
        """
        :type equations: List[List[str]]
        :type values: List[float]
        :type queries: List[List[str]]
        :rtype: List[float]
        """
        # Create a graph of variables, where edges are multipliers
        multiplier_graph = {}

        for i in range(len(equations)):
            if equations[i][0] not in multiplier_graph:
                multiplier_graph[equations[i][0]] = []
            if equations[i][1] not in multiplier_graph:
                multiplier_graph[equations[i][1]] = []
            multiplier_graph[equations[i][0]].append((equations[i][1], values[i]))
            multiplier_graph[equations[i][1]].append((equations[i][0], 1/values[i]))

        answers = []

        for query in queries:
            if query[0] not in multiplier_graph or query[1] not in multiplier_graph:
                answers.append(-1)
            else:  
                def dfs(num1, num2,visited):
                    if num1 == num2:
                        return 1
                    visited.add(num1)
                    for num_multiplier_pair in multiplier_graph[num1]:
                        neighbor, multiplier = num_multiplier_pair
                        if neighbor not in visited:
                            result = dfs(neighbor, num2, visited)
                            if result is not None:
                                return result * multiplier
                    return None
                
                multiplier = dfs(query[0], query[1],set())
                if multiplier is not None:
                    answers.append(multiplier)
                else:
                    answers.append(-1)

        return answers
