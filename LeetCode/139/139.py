class Solution(object):
    def wordBreak(self, s, wordDict):
        """
        :type s: str
        :type wordDict: List[str]
        :rtype: bool
        """
        # Recursion
        '''
        def wordBreakHelper(i):
            if i == len(s):
                return True


            for key in wordDict:
                word = s[i:i+len(key)]
                if word == key and wordBreakRecursive(i+len(key)):
                    return True
            
            return False

        return wordBreakRecursive(0)
        '''

        # Recursion with memo
        '''
        memo = {}
        def wordBreakHelper(i):
            if i == len(s):
                return True

            if i in memo:
                return memo[i]

            for key in wordDict:
                word = s[i:i+len(key)]
                if word == key and wordBreakHelper(i+len(key)):
                    memo[i] = True
                    return True
            
            memo[i] = False
            return False

        return wordBreakHelper(0)
        '''

        # DP
        dp = [False] * (len(s)+1)
        dp[-1] = True

        for i in range(len(s)-1,-1,-1):
            for key in wordDict:
                word = s[i:min(i+len(key), len(s))]
                if word == key and dp[min(i+len(key), len(s))]:
                    dp[i] = True
        return dp[0]
