# Tree Data Structure

Non-linear data structure. Nodes have to parts: data and a link.

Example uses: hierarchical data, files and folders, XML/HTML data

Types of trees: Binary search trees, AVL, Red Black Tree, Trie

### Tree Terminology

Root: top node without a parent

Edge: a link between parent and child

Sibling: children of the same parent

Ancestor: parent, grandparent, great grandparent of a node

Depth of node: a length of the path from root to node

Height of node: a length of the path form the node to the deepest node

Depth of tree: depth of root node (always 0)

Height of tree: height of root node

### Creating a tree:

```Python
class TreeNode:
    def __init__(self, data, children = []):
        self.data = data
        self.children = children

    def __str__(self, level = 0):
        ret = " " * level + str(self.data) + "\n"
        for child in self.children:
            ret += child.__str__(level + 1)
        return ret
    def addChild(self, TreeNode):
        self.children.append(TreeNode)

#example
tree = TreeNode('Drinks', [])
cold = TreeNode('Cold', [])
hot = TreeNode('Hot', [])
tree.addChild(cold)
tree.addChild(hot)
tea = TreeNode('tea', [])
coffee = TreeNode('coffee', [])
cola = TreeNode('cola', [])
fanta = TreeNode('fanta', [])
cold.addChild(cola)
cold.addChild(fanta)
hot.addChild(tea)
hot.addChild(coffee)
print(tree)
```

Time complexity: O(1)

Space complexity: O(1)

# Binary Tree

Definition: data structures in which each node has at most tow children, often referred to as the left and right children.

Tree examples: BST, Heap tree, AVL, red black tress, Syntax trees

### Types of binary tree:

Full binary tree: each node has 2 children or no children

Perfect binary tree: each node has 2 children, all leaf nodes are at the same level

Complete binary tree: all levels are filled, except last level, which has all notes to the left as much as possible

Balanced binary tree: binary tree in which the height of the left and right subtree of any node differ by not more than 1.

### Binary Tree Representation:

Linked list.

Array:

- Index 0 is empty
    
- Left child = cell[2 * parentIndex]
    
- Right child = cell[2 * parentIndex + 1]

Linked list binary tree operations:
- Creation of a tree
- Insertion of a node
- Deletion of a node
- Search for a value
- Traverse all nodes
- Deletion of tree

# Binary Tree Traversal

## PreOrder Traversal

Root Node -> Left Subtree -> Right Subtree

```Python
class TreeNode:
    def __init__(self, data):
        self.data = data
        self.leftChild = None
        self.rightChild = None

newBT = TreeNode("Drinks")
leftChild = TreeNode("Hot")
rightChild = TreeNode("Cold")
newBT.leftChild = leftChild
newBT.rightChild = rightChild

def preOrderTraversal(rootNode):
    if not rootNode:
        return
    print(rootNode.data)
    preOrderTraversal(rootNode.leftChild)
    preOrderTraversal(rootNode.rightChild)

preOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

## InOrder Traversal

Left Subtree -> Root Node -> Right Subtree

```Python
def inOrderTraversal(rootNode):
    if not rootNode:
        return
    inOrderTraversal(rootNode.leftChild)
    print(rootNode.data)
    inOrderTraversal(rootNode.rightChild)

inOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

## PostOrder Traversal

Left Subtree -> Right Subtree -> Root Node

```Python
def postOrderTraversal(rootNode):
    if not rootNode:
        return
    postOrderTraversal(rootNode.leftChild)
    postOrderTraversal(rootNode.rightChild)
    print(rootNode.data)

postOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

## LevelOrder Traversal

Level by level, left to right

```Python
import QueueLinkedList as queue

def levelOrderTraversal(rootNode):
    if not rootNode:
        return
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not(customQueue.isEmpty()):
            root = customQueue.dequeue()
            print(root.value.data)
            if (root.value.leftChild is not None):
                customQueue.enqueue(root.value.leftChild)

            if (root.value.rightChild is not None):
                customQueue.enqueue(root.value.rightChild)

levelOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

# Searching for a node in a binary tree

Use level order traversal because queue performs better than a stack.

```Python
def searchBT(rootNode, nodeValue):
    if not rootNode:
        return "The BT does not exist"
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not (customQueue.isEmpty()):
            root = customQueue.dequeue()
            if root.value.data == nodeValue:
                return "Success"
            if (root.value.leftChild is not None):
                customQueue.enqueue(root.value.leftChild)

            if (root.value.rightChild is not None):
                customQueue.enqueue(root.value.rightChild)
        return "Nof found"

print(searchBT(newBT, "Tea"))
```

Time complexity: O(N)

Space complexity: O(N)

# Inserting a node in a binary tree

- A root node is blank

- The tree exist and we have to look for a first vacant place

Use level order traversal and insert at the first found empty node.

```Python
def insertNodeBT(rootNode, newNode):
    if not rootNode:
        rootNode = newNode
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not (customQueue.isEmpty()):
            root = customQueue.dequeue()
            if root.value.leftChild is not None:
                customQueue.enqueue(root.value.leftChild)
            else:
                root.value.leftChild = newNode
                return "Successfully inserted"

            if root.value.rightChild is not None:
                customQueue.enqueue(root.value.rightChild)
            else:
                root.value.rightChild = newNode
                return "Successfully inserted"

newNode = TreeNode("Cola")
print(insertNodeBT(newBT, newNode))
levelOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

# Deleting a node from a binary tree

Replace node value with deepest node (last node in level order traversal) value. Then delete the deepest node.

```Python
def getDeepestNode(rootNode):
    if not rootNode:
        return
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not(customQueue.isEmpty()):
            root = customQueue.dequeue()
            if (root.value.leftChild is not None):
                customQueue.enqueue(root.value.leftChild)

            if (root.value.rightChild is not None):
                customQueue.enqueue(root.value.rightChild)
        deepestNode = root.value
        return deepestNode

def deleteDeepestNode(rootNode, dNode):
    if not rootNode:
        return
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not(customQueue.isEmpty()):
            root = customQueue.dequeue()
            if root.value is dNode:
                root.value = None
                return
            if root.value.rightChild:
                if root.value.rightChild is dNode:
                    root.value.rightChild = None
                    return
                else:
                    customQueue.enqueue(root.value.rightChild)
            if root.value.leftChild:
                if root.value.leftChild is dNode:
                    root.value.leftChild = None
                    return
                else:
                    customQueue.enqueue(root.value.leftChild)

def deleteNodeBT(rootNode, node):
    if not rootNode:
        return "The BT does not exist"
    else:
        customQueue = queue.Queue()
        customQueue.enqueue(rootNode)
        while not(customQueue.isEmpty()):
            root = customQueue.dequeue()
            if root.value.data == node:
                dNode = getDeepestNode(rootNode)
                root.value.data = dNode.data
                deleteDeepestNode(rootNode, dNode)
                return "The node has been successfully deleted"
            if (root.value.leftChild is not None):
                customQueue.enqueue(root.value.leftChild)

            if (root.value.rightChild is not None):
                customQueue.enqueue(root.value.rightChild)
        return "Failed to delete"

deleteNodeBT(newBT, "Hot")
levelOrderTraversal(newBT)
```

Time complexity: O(N)

Space complexity: O(N)

# Delete the entire binary tree

Set rootNode to none and delete the link before root and left and right child.

```Python
def deleteBT(rootNode):
    rootNode.data = None
    rootNode.leftChild = None
    rootNode.rightChild = None
    return "The BT has been succesfully deleted"

deleteBT(newBT)
levelOrderTraversal(newBT)
```

Time complexity: O(1)

Space complexity: O(1)

# Create binary tree using python list

First cell is empty.

Left child = cell[2x]

Right child = cell[2x+1]

```Python
class BinaryTree:
    def __init__(self, size):
        self.customList = size * [None]
        self.lastUsedIndex = 0
        self.maxSize = size

newBT = BinaryTree(8)
```

Time complexity: O(1)

Space complexity: O(N)

# Insert a node into a binary tree

2 cases:

- Tree is full

- Tree is not full. We look for first vacant place.

```Python
    def insertNode(self, value):
        if self.lastUsedIndex + 1 == self.maxSize:
            return "The binary tree is full"
        self.customList[self.lastUsedIndex+1] = value
        self.lastUsedIndex += 1
        return "The value has been successfully inserted"

newBT = BinaryTree(8)
print(newBT.insertNode("Drinks"))
print(newBT.insertNode("Hot"))
print(newBT.insertNode("Cold"))
```

Time complexity: O(1)

Space complexity: O(1)

# Searching for a node in binary tree

```Python
def searchNode(self, nodeValue):
        for i in range(len(self.customList)):
            if self.customList[i] == nodeValue:
                return "Success"
        return "Not found"

newBT = BinaryTree(8)
print(newBT.insertNode("Drinks"))
print(newBT.insertNode("Hot"))
print(newBT.insertNode("Cold"))

print(newBT.searchNode("Tea"))
print(newBT.searchNode("Hot"))
```

Time complexity: O(N)

Space complexity: O(1)

# Preorder traversal of a binary tree

root node -> left subtree -> right subtree

```Python
def preOrderTraversal(self, index):
        if index > self.lastUsedIndex:
            return
        print(self.customList[index])
        self.preOrderTraversal(index*2)
        self.preOrderTraversal(index*2+1)


newBT = BinaryTree(8)
print(newBT.insertNode("Drinks"))
print(newBT.insertNode("Hot"))
print(newBT.insertNode("Cold"))
newBT.insertNode("Tea")
newBT.insertNode("Coffee")

print(newBT.searchNode("Tea"))
print(newBT.searchNode("Hot"))

newBT.preOrderTraversal(1)
```

Time complexity: O(N)

Space complexity: O(1)

# Inorder traversal of a binary tree

left subtree -> root node -> right subtree

```Python
def inOrderTraversal(self, index):
        if index > self.lastUsedIndex:
            return
        self.inOrderTraversal(index*2)
        print(self.customList[index])
        self.inOrderTraversal(index*2+1)

newBT = BinaryTree(8)
print(newBT.insertNode("Drinks"))
print(newBT.insertNode("Hot"))
print(newBT.insertNode("Cold"))
newBT.insertNode("Tea")
newBT.insertNode("Coffee")

print(newBT.searchNode("Tea"))
print(newBT.searchNode("Hot"))

print("\n")
newBT.preOrderTraversal(1)
print("\n")
newBT.inOrderTraversal(1)
```
Time complexity: O(N)

Space complexity: O(1)

# Postorder traversal of a binary tree

left subtree -> right subtree -> root node

```Python
def postOrderTraversal(self, index):
        if index > self.lastUsedIndex:
            return
        self.postOrderTraversal(index*2)
        self.postOrderTraversal(index*2+1)
        print(self.customList[index])
```

Time complexity: O(N)

Space complexity: O(1)

# LevelOrder traversal of a binary tree

```Python
def levelOrderTraversal(self, index):
        for i in range(index, self.lastUsedIndex+1):
            print(self.customList[i])
```

Time complexity: O(N)

Space complexity: O(1)

# Delete a node from a binary tree

Find the deepest node in the tree (last node during level order traversal, last used index in list). Swap the node with the deepest node, delete the deepest node


```Python
def deleteNode(self, value):
        if self.lastUsedIndex == 0:
            return "The tree is empty"
        for i in range(1, self.lastUsedIndex+1):
            if self.customList[i] == value:
                self.customList[i] = self.customList[self.lastUsedIndex]
                self.customList[self.lastUsedIndex] = None
                self.lastUsedIndex -= 1
                return "The node has been successfully deleted"
```

Time complexity: O(N)

Space complexity: O(1)

# Delete entire binary tree 

Update list to None

```Python
def deleteBT(self):
        self.customList = None
        return "The BT has been successfully deleted"
```

Time complexity: O(1)

Space complexity: O(1)
