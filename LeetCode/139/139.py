class Solution(object):
    def wordBreak(self, s, wordDict):
        """
        :type s: str
        :type wordDict: List[str]
        :rtype: bool
        """
        # traverse the word. On every letter we can add it to the current word or start new word
        dp = [False] * len(s)

        for i in range(len(s)-1,-1,-1):
            for key in wordDict:
                if i+len(key) >= len(s):
                    word = s[i:len(s)]
                    if word == key:
                        dp[i] = True
                else:
                    word = s[i:i+len(key)]
                    if word == key and dp[i+len(key)]:
                        dp[i] = True
        return dp[0]

test = Solution()
print(test.wordBreak("leetcode", ["leet","code"]))
print(test.wordBreak("applepenapple", ["apple","pen"]))
print(test.wordBreak("catsandog", ["cats","dog","sand","and","cat"]))
print(test.wordBreak("aaaaaaa", ["aaaa","aaa"]))
print(test.wordBreak("cars", ["car","ca","rs"]))
print(test.wordBreak("cars", ["ca","rs","car"]))
print(test.wordBreak("ab", ["a","b"]))
