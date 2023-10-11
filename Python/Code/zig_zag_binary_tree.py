class TreeNode(object):
    def __init__(self, val=0, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right

class Solution(object):
    def longest_zig_zag_tree(self, root, max_length):
        if not root:
            return
        max_length = max(max_length, self.longest_zig_zag_node(root.left, "left"),
                                     self.longest_zig_zag_node(root.right, "right"))
        self.longest_zig_zag_tree(root.left, max_length)
        self.longest_zig_zag_tree(root.right, max_length)
        return max_length

    def longest_zig_zag_node(self, node, curr_dir):
        if not node:
            return 0
        
        if curr_dir == "right":
            return 1 + self.longest_zig_zag_node(node.left, "left")
        if curr_dir == "left":
            return 1 + self.longest_zig_zag_node(node.right, "right")

eight_node = TreeNode(1)
seven_node = TreeNode(1, None, eight_node)
six_node = TreeNode(1)
five_node = TreeNode(1, None, seven_node)
four_node = TreeNode(1, five_node, six_node)
three_node = TreeNode(1)
two_node = TreeNode(1, three_node, four_node)
one_node = TreeNode(1, None, two_node)

test = Solution()
print(test.longest_zig_zag_node(four_node, "right"))
max_length = 0
print(test.longest_zig_zag_tree(one_node, max_length))