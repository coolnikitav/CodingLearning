class Solution(object):
    def findMaxForm(self,strs, m, n):
        dp = [[0] * (n+1) for _ in range(m+1)]
        for str in strs:
            one = 0
            zero = 0
            for c in str:
                if c == '1':
                    one += 1
                else:
                    zero += 1
            for i in range(m, zero-1, -1):
                for j in range(n, one-1, -1):
                    if one <= j and zero <= i:
                        dp[i][j] = max(dp[i][j], dp[i-zero][j-one] + 1)
        return dp[m][n]

test = Solution()
print(test.findMaxForm(["10","0001","111001","1","0"], 5, 3))
print(test.findMaxForm(["10","0","1"], 1, 1))
print(test.findMaxForm(["10","0001","111001","1","0"], 4, 3))
print(test.findMaxForm(["11111","100","1101","1101","11000"], 5, 7))
