# Definition for singly-linked list.
class ListNode(object):
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next
class Solution(object):
    def mergeTwoLists(self, list1, list2):
        """
        :type list1: Optional[ListNode]
        :type list2: Optional[ListNode]
        :rtype: Optional[ListNode]
        """
        if not list1 or not list2:
            return list1 or list2
        if list1.val < list2.val:
            list1.next = self.mergeTwoLists(list1.next, list2)
            return list1
        else:
            list2.next = self.mergeTwoLists(list1, list2.next)
            return list2
        
example = Solution()

list1 = ListNode(1)
list1node2 = ListNode(3)
list1.next = list1node2
list1node3 = ListNode(4)
list1node2.next = list1node3

list2 = ListNode(1)
list2node2 = ListNode(2)
list2.next = list2node2
list2node3 = ListNode(4)
list2node2.next = list2node3

mergedlist = example.mergeTwoLists(list1, list2)

while mergedlist:
    print(mergedlist.val)
    mergedlist = mergedlist.next