# Definition for singly-linked list.
# class ListNode(object):
#     def __init__(self, val=0, next=None):
#         self.val = val
#         self.next = next
class Solution(object):
    def reverseList(self, head):
        """
        :type head: ListNode
        :rtype: ListNode
        """

        # Create a new list to hold the reversed list
        reversed_head = None

        # Traverse the original list
        # Go to the second node and then append the first node to the reversed list
        curr = head
        while curr:
            next_node = curr.next
            curr.next = reversed_head
            reversed_head = curr
            curr = next_node
        
        return reversed_head
