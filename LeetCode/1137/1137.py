class Solution(object):
    def tribonacci(self, n):
        """
        :type n: int
        :rtype: int
        """
        def tribonaci_memo(n,memo):
            if n == 0:
                return 0
            if n == 1:
                return 1
            if n == 2:
                return 1
            if n not in memo:
                memo[n] = tribonaci_memo(n-1,memo) + tribonaci_memo(n-2,memo) + tribonaci_memo(n-3,memo)
            return memo[n]
        memo = {}
        return tribonaci_memo(n,memo)
