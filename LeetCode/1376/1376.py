class Solution:
    def numOfMinutes(self, n: int, headID: int, manager: List[int], informTime: List[int]) -> int:
        # create a graph from manager arr in the form of { manager: [employees]}
        # do a DFS on the graph starting at headID and find the max sum using informTime
        manager_employees = {}
        for i in range(len(manager)):
            if manager[i] not in manager_employees:
                manager_employees[manager[i]] = [i]
            else:
                manager_employees[manager[i]].append(i)
        
        def dfs(id):
            if id not in manager_employees.keys():  # not a manager
                return 0
            cur_max = 0
            for employee in manager_employees[id]:
                cur_max = max(cur_max, informTime[employee] + dfs(employee))          
            return cur_max
        return dfs(-1)
