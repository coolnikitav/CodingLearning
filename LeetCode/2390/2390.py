class Solution(object):
    def removeStars(self, s):
        """
        :type s: str
        :rtype: str
        """
        stack = []

        for ch in s:
            if ch == "*":
                stack.pop()
            else:
                stack.append(ch)
    
        return ''.join(stack)
