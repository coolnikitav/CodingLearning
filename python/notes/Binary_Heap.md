# A Binary Heap is a Binary Tree with following properties:
A BH is either Min Heap or Max Heap. In a Min BH, the key at root must be minimum among all keys present in BH. The same property must be recursively true for all nodes in Binary Tree.

It's a complete tree (All levels are completely filled except possibly the last level and the last level has all keys as left as possible). This property of BH makes them suitable to be stored in an array.

# Why we need a binary heap?
Find the minumum or maximum number among a set of numbers in logN time. And also we want to make sure that inserting additional numbers does not take more than logN time.

Possible solutions:
- Store the numbers in sorted array. Find min: O(1), insertion: O(n)
- Store the numbers in Linked List in sorted manner

Practical use:
- Prim's algorithm
- Heap sort
- Priority queue

# Types of binary heap
Min heap

Max heap

# Common operations on Binary Heap
- Creation of Binary Heap
- Peek top
- Extract min/max
- Traversal
- Size of Binary Heap
- Insert value
- Delete the entire Binary Heap

Implementation Options
- Array implementation
- Reference/pointer implementation

# Creation of Binary Heap (array)
```Python
class Heap:
    def __init__(self, size):
        self.customList = (size+1) * [None]
        self.heapSize = 0
        self.maxSize = size + 1
newBinaryHeap = Heap(5)
```
Time complexity: O(1)

Space complexity: O(N)

# Peek top
```Python
def peekOfHeap(rootNode):
    if not rootNode:
        return
    else:
        return rootNode.customList[1]

```
Time complexity: O(1)

Space complexity: O(1)

# Size of Binary Heap
```Python
def sizeofHeap(rootNode):
    if not rootNode:
        return
    else:
        return rootNode.heapSize
    
print(sizeofHeap(newBinaryHeap))
```
Time complexity: O(1)

Space complexity: O(1)

# LevelOrder Traversal
```Python
def levelOrderTraversal(rootNode):
    if not rootNode:
        return
    else:
        for i in range(1, rootNode.heapSize+1):
            print(rootNode.customList[i])

levelOrderTraversal(newBinaryHeap)
```

Time complexity: O(N)

Space complexity: O(1)

# Inserting a node

Find first unused cell in the array
```Python
def heapifyTreeInsert(rootNode, index, heapType):
    parentIndex = int(index/2)
    if index <= 1:
        return
    if heapType == "Min":
        if rootNode.customList[index] < rootNode.customList[parentIndex]:
            temp = rootNode.customList[index]
            rootNode.customList[index] = rootNode.customList[parentIndex]
            rootNode.customList[parentIndex] = temp
        heapifyTreeInsert(rootNode, parentIndex, heapType)
    elif heapType == "Max":
        if rootNode.customList[index] > rootNode.customList[parentIndex]:
           temp = rootNode.customList[index]
           rootNode.customList[index] = rootNode.customList[parentIndex]
           rootNode.customList[parentIndex] = temp 
        heapifyTreeInsert(rootNode, parentIndex, heapType)     

def insertNode(rootNode, nodeValue, heapType):
    if rootNode.heapSize + 1 == rootNode.maxSize:
        return "The Binary Heap is full"
    rootNode.customList[rootNode.heapSize + 1] = nodeValue
    rootNode.heapSize += 1
    heapifyTreeInsert(rootNode, rootNode.heapSize, heapType)   
    return "The value has been successfully inserted"

insertNode(newHeap, 4, "Max")
insertNode(newHeap, 5, "Max")
insertNode(newHeap, 2, "Max")
insertNode(newHeap, 1, "Max")
levelOrderTraversal(newHeap)
```
Time complexity: O(logN)

Space complexity: O(logN)

# Extract a node from Binary Heap
Only allowed to extract the root node.

Switch root node with last node. Heapify the tree.

```Python
def heapifyTreeInsert(rootNode, index, heapType):
    leftIndex = index * 2
    rightIndex = index * 2 + 1
    swapChild = 0

    if rootNode.heapSize < leftIndex:
        return
    elif rootNode.heapSize == leftIndex:
        if heapType == "Min":
            if rootNode.customList[index] > rootNode.customList[leftIndex]:
                temp = rootNode.customList[index]
                rootNode.customList[index] = rootNode.customList[leftIndex]
                rootNode.customList[leftIndex] = temp
            return
        else:
            if rootNode.customList[index] < rootNode.customList[leftIndex]:
                temp = rootNode.customList[index]
                rootNode.customList[index] = rootNode.customList[leftIndex]
                rootNode.customList[leftIndex] = temp
            return
    else:
        if heapType == "Min":
            if rootNode.customList[leftIndex] < rootNode.customList[rightIndex]:
                swapChild = leftIndex
            else:
                swapChild = rightIndex
            if rootNode.customList[index] > rootNode.customList[swapChild]:
                temp = rootNode.customList[index]
                rootNode.customList[index] = rootNode.customList[swapChild]
                rootNode.customList[swapChild] = temp
        else:
            if rootNode.customList[leftIndex] > rootNode.customList[rightIndex]:
                swapChild = leftIndex
            else:
                swapChild = rightIndex
            if rootNode.customList[index] < rootNode.customList[swapChild]:
                temp = rootNode.customList[index]
                rootNode.customList[index] = rootNode.customList[swapChild]
                rootNode.customList[swapChild] = temp
        heapifyTreeInsert(rootNode, swapChild, heapType)

def extractNode(rootNode, heapType):
    if rootNode.heapSize == 0:
        return
    else: 
        extractedNode = rootNode.customList[1]
        rootNode.customList[1] = rootNode.customList[rootNode.heapSize]
        rootNode.customList[rootNode.heapSize] = None
        rootNode.heapSize -= 1
        heapifyTreeInsert(rootNode, 1, heapType)
        return extractedNode

print(extractNode(newHeap, "Max"))
levelOrderTraversal(newHeap)
```
Time complexity: O(logN)

Space complexity: O(logN)

# Delete the entire Binary Heap
```Pyhon
def deleteEntireBH(rootNode):
    rootNode.customList = None

deleteEntireBH(newHeap)
levelOrderTraversal(newHeap)
```
Time complexity: O(1)

Space complexity: O(1)
