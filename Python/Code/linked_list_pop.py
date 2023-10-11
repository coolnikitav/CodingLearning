class Node:
    def __init__(self, val):
        self.val = val
        self.next = None

class SinglyLinkedList:
    def __init__(self):
        self.head = None
        self.tail = None
        self.length = 0
    
    def push(self, data):
        node = Node(data)
        if self.head == None:
            self.head = node
        else:
            self.tail.next = node
        self.tail = node
        self.length += 1
        return "Success"
    
    def pop(self):
        # Case 1: the list is empty
        if not self.head:
            return "Undefined"
            
        # Case 2: the list has one item
        if self.head == self.tail:
            pop_node = self.head
            self.head = None
            self.tail = None
        
        # Case 3: the list has more than one item
        else:
            current_node = self.head
            for _ in range(self.length-2):
                current_node = current_node.next
            pop_node = current_node.next
            self.tail = current_node
            self.tail.next = None
            
        self.length -= 1
        
        return pop_node

singlyLinkedList = SinglyLinkedList()
singlyLinkedList.push(5)  # Success
singlyLinkedList.length   # 1
singlyLinkedList.head.val # 5
singlyLinkedList.tail.val # 5
 
singlyLinkedList.push(10)    # Success
singlyLinkedList.length      # 2
singlyLinkedList.head.val    # 5
singlyLinkedList.head.next.val  # 10
singlyLinkedList.tail.val    # 10
 
 
singlyLinkedList.pop().val # 10
singlyLinkedList.tail.val  # 5
singlyLinkedList.length    # 1
singlyLinkedList.pop().val # 5
singlyLinkedList.length    # 0
singlyLinkedList.pop()     # Undefined