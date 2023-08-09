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
