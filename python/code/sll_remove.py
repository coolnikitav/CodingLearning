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
    
    def remove(self, index):
        if index < 0 or index >= self.length or self.length == 0:
            return None
        
        # Case 1: list with one item
        if self.length == 1:
            removed_node = self.head
            self.head = None
            self.tail = None
        
        # Case 2: list with multiple items
        else:
            prev_node = self.head
            for _ in range(index-1):
                prev_node = prev_node.next
                
            removed_node = prev_node.next

            if removed_node == self.tail:
                self.tail = prev_node
                prev_node.next = None
            else:
                prev_node.next = prev_node.next.next
        
        self.length -= 1
        return removed_node

singlyLinkedList = SinglyLinkedList()
singlyLinkedList.push(5)  # Success
singlyLinkedList.push(10)  # Success
singlyLinkedList.push(15)  # Success
singlyLinkedList.push(20)  # Success
singlyLinkedList.push(25)  # Success
singlyLinkedList.remove(2).val # 15
singlyLinkedList.remove(100) # None
print(singlyLinkedList.length)  # 4
singlyLinkedList.head.val   # 5
singlyLinkedList.head.next.val  # 10
singlyLinkedList.head.next.next.val  # 20