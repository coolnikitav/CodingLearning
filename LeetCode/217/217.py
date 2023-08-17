class Solution(object):
    def containsDuplicate(self, nums):
        """
        :type nums: List[int]
        :rtype: bool
        """
        a = set()
        
        for num in nums:
            if num in a:
                return True
            else:
                a.add(num)
        return False
