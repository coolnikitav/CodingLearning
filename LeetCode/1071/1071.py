class Solution(object):
    def gcd(self, num1, num2):
        result = min(num1,num2)
        while result:
            if num1 % result == 0 and num2 % result == 0:
                break
            result -= 1
        return result

    def gcdOfStrings(self, str1, str2):
        """
        :type str1: str
        :type str2: str
        :rtype: str
        """
        if(str1 + str2 != str2 + str1):
            return ""
        else:
            return str1[:self.gcd(len(str1),len(str2))]
