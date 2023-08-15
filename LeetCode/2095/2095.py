# Definition for singly-linked list.
# class ListNode(object):
#     def __init__(self, val=0, next=None):
#         self.val = val
#         self.next = next
class Solution(object):
    def deleteMiddle(self, head):
        """
        :type head: Optional[ListNode]
        :rtype: Optional[ListNode]
        """
        # size = 0
        # curr = head
        # while curr:
        #     size += 1
        #     curr = curr.next
        
        # if size == 1:
        #     head = None
        # elif size == 2:
        #     head.next = None
        # else:
        #     curr = head
        #     for _ in range(0, (size//2)-1):
        #         curr = curr.next
        #     curr.next = curr.next.next
        # return head

        # Edge case: If there is only one node
        if head.next == None:
            return None

        slow = head
        fast = head.next.next

        # Get slow to the middle of the list
        while fast and fast.next:
            slow = slow.next
            fast = fast.next.next
        slow.next = slow.next.next

        return head
