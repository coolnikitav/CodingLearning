# Definition for singly-linked list.
# class ListNode(object):
#     def __init__(self, val=0, next=None):
#         self.val = val
#         self.next = next
class Solution(object):
    def oddEvenList(self, head):
        """
        :type head: ListNode
        :rtype: ListNode
        """

        # Create a new list to store odds and evens
        oddList = ListNode()
        evenList = ListNode()

        # Store the head of each list
        oddHead = oddList
        evenHead = evenList

        odd = True
        while head:
            if odd:
                oddList.next = head
                oddList = oddList.next
            else:
                evenList.next = head
                evenList = evenList.next
            odd = not odd
            head = head.next
        evenList.next = None
        oddList.next = evenHead.next
        return oddHead.next
