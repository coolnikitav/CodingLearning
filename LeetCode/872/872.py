# Definition for a binary tree node.
# class TreeNode(object):
#     def __init__(self, val=0, left=None, right=None):
#         self.val = val
#         self.left = left
#         self.right = right
class Solution(object):
    def leafSimilar(self, root1, root2):
        """
        :type root1: TreeNode
        :type root2: TreeNode
        :rtype: bool
        """

        left = self.traverseTree(root1)
        right = self.traverseTree(root2)

        return left == right

    def traverseTree(self, root):
        if not root:
            return []
        if not root.left and not root.right:
            return [root.val]
        
        left = self.traverseTree(root.left)
        right = self.traverseTree(root.right)
        return left + right
