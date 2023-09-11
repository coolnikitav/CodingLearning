# Definition for a binary tree node.
# class TreeNode(object):
#     def __init__(self, val=0, left=None, right=None):
#         self.val = val
#         self.left = left
#         self.right = right
class Solution(object):
    def goodNodes(self, root):
        """
        :type root: TreeNode
        :rtype: int
        """ 
        return self.dfs(root, root.val)

    def dfs(self, node, cur_max):
        if not node:
            return 0
        if node.val >= cur_max:
            cur_max = node.val
            return 1 + self.dfs(node.left, cur_max) + self.dfs(node.right, cur_max)
        else:
            # Zero added for better visual interpretation
            return 0 + self.dfs(node.left, cur_max) + self.dfs(node.right, cur_max)
