import heapq

class Solution(object):
    def maxScore(self, nums1, nums2, k):
        """
        :type nums1: List[int]
        :type nums2: List[int]
        :type k: int
        :rtype: int
        """

        n = len(nums1)
        nums_pairs = []

        # create (nums2[i],nums1[i]) pairs

        for i in range(n):
            nums_pairs = [(n1,n2) for n1,n2 in zip(nums1,nums2)]

        # sort them into an array
        nums_pairs = sorted(nums_pairs, key=lambda p: p[1], reverse=True)

        minHeap = []
        n1Sum = 0
        max_score = 0

        for n1, n2 in nums_pairs:
            n1Sum += n1
            heapq.heappush(minHeap, n1)

            if len(minHeap) > k:
                n1Pop = heapq.heappop(minHeap)
                n1Sum -= n1Pop
            if len(minHeap) == k:
                max_score = max(max_score, n1Sum * n2)
        

        # return largest score
        return max_score

test = Solution()

print(test.maxScore([1,3,3,2], [2,1,3,4], 3))
print(test.maxScore([4,2,3,1,1], [7,5,10,9,6], 1))
print(test.maxScore([23,16,20,7,3], [19,21,22,22,12], 3))
