class Node:
    def __init__(self, data):
        self.data = data
        self.leftChild = None
        self.rightChild = None

class BST:
    def __init__(self):
        self.root = Node(None)

def insertNode(rootNode, nodeValue):
    if rootNode.data == None:
        rootNode.data = nodeValue
    elif nodeValue <= rootNode.data:
        if rootNode.leftChild is None:
            rootNode.leftChild = Node(nodeValue)
        else:
            insertNode(rootNode.leftChild, nodeValue)
    else:
        if rootNode.rightChild is None:
            rootNode.rightChild = Node(nodeValue)
        else:
            insertNode(rootNode.rightChild, nodeValue)
    return "The node has been successfully inserted"

def removeNode(rootNode, nodeValue):
    if not rootNode:
        return None
    
    if nodeValue < rootNode.data:
        rootNode.leftChild = removeNode(rootNode.left, nodeValue)
    elif nodeValue > rootNode.data:
        rootNode.rightChild = removeNode(rootNode.right, nodeValue)
    else:
        if not rootNode.leftChild:
            temp = rootNode.rightChild
            rootNode = None
            return temp
        if not rootNode.rightChild:
            temp = rootNode.leftChild
            rootNode = None
            return temp
        temp = inOrderSuccessor(rootNode.right)
        rootNode.data = temp.data
        rootNode.rightChild = removeNode(rootNode.right, temp.data)
    return rootNode
    
def inOrderSuccessor(node):
    if not node.leftChild:
        return node
    return inOrderSuccessor(node.leftChild)

bsTree = BST()
insertNode(bsTree.root, 15)
insertNode(bsTree.root, 20)
insertNode(bsTree.root, 10)
insertNode(bsTree.root, 12)
removeNode(bsTree.root, 12)
bsTree.root.rightChild.data #20
bsTree.root.leftChild.data #10
bsTree.root.leftChild.rightChild #None