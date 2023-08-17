class Solution(object):
    def maxSubArray(self, nums):
        """
        :type nums: List[int]
        :rtype: int
        """
        sum = nums[0]
        curr_sum = 0

        for num in nums:
            curr_sum += num
            # Update sum before resetting curr_sum because of case with all negative numbers
            sum = max(curr_sum, sum)    
            if curr_sum < 0:
                curr_sum = 0

        return sum
