class Solution(object):
    def isPerfectSquare(self, num):
        """
        :type num: int
        :rtype: bool
        """
        low = 0
        high = num

        while (low <= high):
            mid = (high+low)//2
            square = mid**2
            if square == num:
                return True
            elif square > num:
                high = mid-1
            else:
                low = mid+1
        return False
