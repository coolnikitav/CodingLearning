class MaxHeap:
    def __init__(self, size):
        self.customList = (size+1) * [None]
        self.heapSize = 0
        self.maxSize = size + 1

def insertNode(rootNode, nodeValue):
    # Check if heap is full
    if rootNode.heapSize == rootNode.maxSize-1:
        return "The Binary Heap is full"
    current_index = rootNode.heapSize+1
    rootNode.customList[current_index] = nodeValue
    while current_index > 1 and rootNode.customList[current_index//2] < nodeValue:
        rootNode.customList[current_index//2],rootNode.customList[current_index] = rootNode.customList[current_index],rootNode.customList[current_index//2]
        current_index = current_index//2
    rootNode.heapSize += 1
    return rootNode

newHeap = MaxHeap(5)
insertNode(newHeap,4)
insertNode(newHeap,5)
insertNode(newHeap,2)
insertNode(newHeap,1)
insertNode(newHeap,6)
insertNode(newHeap,10) # The Binary Heap is full
newHeap.customList   # [None, 6, 5, 2, 1, 4]
print(newHeap.customList)