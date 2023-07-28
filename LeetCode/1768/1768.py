class Solution(object):
    def mergeAlternately(self, word1, word2):
        """
        :type word1: str
        :type word2: str
        :rtype: str
        """
        len1 = len(word1)
        len2 = len(word2)

        output = ""
        length = len1 if len1 > len2 else len2

        for i in range(length):
            if (i < len1):
                output += word1[i]
            if (i < len2):
                output += word2[i]
        
        return output
