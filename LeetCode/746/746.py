class Solution(object):
    def minCostClimbingStairs(self, cost):
        """
        :type cost: List[int]
        :rtype: int
        """
        cost_len = len(cost)
        memo = [0] * (cost_len+1)

        for i in range(2,cost_len+1):
            memo[i] = min(memo[i-1]+cost[i-1],memo[i-2]+cost[i-2])
        
        return memo[cost_len]
