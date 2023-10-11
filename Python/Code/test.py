class Node:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.right = right
        self.left = left

def getParent(node, root):
    if not root:
        return None
    if (root.left and root.left == node) or (root.right and root.right == node):
        return root
    
    left_parent = getParent(node, root.left)
    right_parent = getParent(node, root.right)
    return left_parent if left_parent else right_parent

root = Node(55)
node44 = Node(44)
node77 = Node(77)
node22 = Node(22)
node99 = Node(99)
node35 = Node(35)
node88 = Node(88)
node90 = Node(90)
node95 = Node(95)
node54 = Node(54)
node33 = Node(33)
root.left = node44
root.right = node77
node44.left = node22
node44.right = node99
node22.left = node35
node22.right = node88
node99.left = node90
node99.right = node95
node88.left = node54
node90.right = node33

parent = getParent(node95, root)
print(parent.value)

def areNodesRelated(child, parent):
    if not parent:
        return False
    if parent == child:
        return True
    left_parent = areNodesRelated(child, parent.left)
    right_parent = areNodesRelated(child, parent.right)
    return left_parent if left_parent else right_parent

print(areNodesRelated(node35, root))

def findFirstCommonAncestor(n1, n2, root):
    n1Parent = getParent(n1, root)

    while n1Parent:
        if areNodesRelated(n2, n1Parent):
            return n1Parent
        n1Parent = getParent(n1Parent, root)
    return None

print(findFirstCommonAncestor(node88, node33, root).value)