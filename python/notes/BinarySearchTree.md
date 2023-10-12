# Binary search tree

## Common operations on binary search tree
- Creation of tree
- Insertion of a node
- Deletion of a node
- Search for a value
- Traverse all nodes
- Deletion of tree

## Creation of a BST
```Python
class BSTNode:
    def __init__(self, data):
        self.data = data
        self.leftChild = None
        self.rightChild = None

newBST = BSTNode(None)
```
Time complexity: O(1)

Space complexity: O(1)

## Inserting a node
2 cases:
- Tree is empty
- Tree is not empty
```Python
def insertNode(rootNode, nodeValue):
    if rootNode.data == None:
        rootNode.data = nodeValue
    elif nodeValue <= rootNode.data:
        if rootNode.leftChild is None:
            rootNode.leftChild = BSTNode(nodeValue)
        else:
            insertNode(rootNode.leftChild, nodeValue)
    else:
        if rootNode.rightChild is None:
            rootNode.rightChild = BSTNode(nodeValue)
        else:
            insertNode(rootNode.rightChild, nodeValue)
    return "The node has been successfully inserted"

print(insertNode(newBST, 70))
print(insertNode(newBST, 60))
print(newBST.data)
print(newBST.leftChild.data)
```
Time complexity: O(logN)

Space complexity: O(logN)

## Traverse the BST

### Preorder traversal
```Python
def preOrderTraversal(rootNode):
    if not rootNode:
        return
    print(rootNode.data)
    preOrderTraversal(rootNode.leftChild)
    preOrderTraversal(rootNode.rightChild)

preOrderTraversal(newBST)
```
Time complexity: O(N)

Space complexity: O(N)

### Inorder traversal
```Python
def inOrderTraversal(rootNode):
    if not rootNode:
        return
    inOrderTraversal(rootNode.leftChild)
    print(rootNode.data)
    inOrderTraversal(rootNode.rightChild)

print("\n")
inOrderTraversal(newBST)
```
Time complexity: O(N)

Space complexity: O(N)

### Postorder traversal
```Python
def postOrderTraversal(rootNode):
    if not rootNode:
        return
    postOrderTraversal(rootNode.leftChild)
    postOrderTraversal(rootNode.rightChild)
    print(rootNode.data)

print("\n")
postOrderTraversal(newBST)
```
Time complexity: O(N)

Space complexity: O(N)

### Levelorder traversal

```Python
def levelOrderTraversal(rootNode):
    if not rootNode:
        return
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not(customQueue.isEmpty()):
            root = customQueue.dequeue()
            print(root.value.data)
            if root.value.leftChild is not None:
                customQueue.enqueue(root.value.leftChild)
            if root.value.rightChild is not None:
                customQueue.enqueue(root.value.rightChild)

print("\n")
levelOrderTraversal(newBST)
```
Time complexity: O(N)

Space complexity: O(N)

### Search for a node in the BST
```Python
def searchNode(rootNode, nodeValue):
    if rootNode.data == nodeValue:
        print("The value is found")
    elif nodeValue < rootNode.data:
        if rootNode.leftChild.data == nodeValue:
            print("The value is found")
        else:
            searchNode(rootNode.leftChild, nodeValue)
    else:
        if rootNode.rightChild.data == nodeValue:
            print("The value is found")
        else:
            searchNode(rootNode.rightChild, nodeValue)

searchNode(newBST, 30)
```
Time complexity: O(logN)

Space complexity: O(logN)

### Deleting a node
3 cases:
- The node to be deleted is a leaf node
- The node has one child
- The node has two children. Successor of the node is the smallest node in the right subtree.
```Python
def deleteNode(rootNode, nodeValue):
    if rootNode is None:
        return rootNode
    if nodeValue < rootNode.data:
        rootNode.leftChild = deleteNode(rootNode.leftChild, nodeValue)
    elif nodeValue > rootNode.data:
        rootNode.rightChild = deleteNode(rootNOde.rightChild, nodeValue)
    else:
        if rootNode.leftChild is None:
            temp = rootNode.rightChild
            rootNode = None
            return temp

        if rootNode.rightChild is None:
            temp = rootNode.leftChild
            rootNode = None
            return temp

        temp = minValueNode(rootNode.right)
        rootNode.data = temp.data
        rootNode.rightChild = deleteNode(rootNode.rightChild, temp.data)
    return rootNode

print("\n")
deleteNode(newBST, 20)
levelOrderTraversal(newBST)
```
Time complexity: O(logN)

Space complexity: O(logN)

### Deleting entire BST
Delete the root node. The rest of the tree becomes eligible for garbage collection.
```Python
def deleteBST(rootNode):
    rootNode.data = None
    rootNode.leftChild = None
    rootNode.rightChild = None
    return "BST has been deleted"
```
Time complexity: O(1)

Space complexity: O(1)
