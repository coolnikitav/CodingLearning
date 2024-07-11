class Solution(object):
    def maxSumAfterPartitioning(self, arr, k):
        """
        :type arr: List[int]
        :type k: int
        :rtype: int
        """
        # 2 options: include into partition or start new partition
        # keep track of highest number and size
        # end everything when traversed through arr
        # add to sum when choose start new partition or traversed through arr
        # if partition size == k, then we can only start new partition

        # recursively 
        """
        def maxSum(i):
            if i == len(arr):
                return 0

            cur_max = 0
            res = 0

            for j in range(i, min(len(arr), i+k)):
                cur_max = max(cur_max, arr[j])
                window_size = j-i+1
                res = max(res, maxSum(j+1) + cur_max * window_size)

            return res

        return maxSum(0)
        """

        # recursively with memo
        """
        cache = {}
        def maxSum(i):
            if i in cache:
                return cache[i]

            cur_max = 0
            res = 0

            for j in range(i, min(len(arr), i+k)):
                cur_max = max(cur_max, arr[j])
                window_size = j-i+1
                res = max(res, maxSum(j+1) + cur_max * window_size)

            cache[i] = res
            return res

        return maxSum(0)
        """

        # dp
        # make our dp structure
        # traverse the arr
        # fill in the structure
        dp = [0] * len(arr)
        for i in range(len(arr)):
            cur_max = 0
            res = 0
            for j in range(i, i-k, -1):
                if j < 0:
                    break
                cur_max = max(cur_max, arr[j])
                window_size = i-j+1
                res = max(res, dp[j-1] + cur_max * window_size)
            dp[i] = res
        return dp[len(arr)-1]
