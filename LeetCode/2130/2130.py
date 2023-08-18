# Definition for singly-linked list.
# class ListNode(object):
#     def __init__(self, val=0, next=None):
#         self.val = val
#         self.next = next
class Solution(object):
    def pairSum(self, head):
        """
        :type head: Optional[ListNode]
        :rtype: int
        """
        temp_list = []
        twin_sum = 0

        curr = head
        while curr:
            temp_list.append(curr.val)
            curr = curr.next
        
        length = len(temp_list)
        for i in range(0, length//2):
            twin_sum = max(twin_sum, temp_list[i] + temp_list[length-1-i])

        return twin_sum
