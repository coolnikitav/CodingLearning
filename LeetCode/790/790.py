class Solution(object):
    def numTilings(self, n):
        """
        :type n: int
        :rtype: int
        """
        if n == 1:
            return 1
        if n == 2:
            return 2
        if n == 3:
            return 5

        memo = [0]*(n+1)
        memo[1] = 1
        memo[2] = 2
        memo[3] = 5
        
        for i in range(4,n+1):
            memo[i] = memo[i-1]*2 + memo[i-3]
        
        return memo[n]%(pow(10,9)+7)
