# Definition for singly-linked list.
# class ListNode(object):
#     def __init__(self, val=0, next=None):
#         self.val = val
#         self.next = next
class Solution(object):
    def removeElements(self, head, val):
        """
        :type head: ListNode
        :type val: int
        :rtype: ListNode
        """
        if not head:
            return None

        # Chain the nodes together
        head.next = self.removeElements(head.next, val)

        # If the node does not need to be removed,
        # chain node to the list
        if head.val != val:
            return head 
        # If the node does need to be removed,
        # move to the next node to check it 
        else:
            return head.next
