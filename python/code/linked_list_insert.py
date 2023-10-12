#   Created by Elshad Karimov 
#   Copyright © AppMillers. All rights reserved.

# Singly Linked List

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
    
    def insert(self, index, data):
        # Case 1: invalid index
        if index < 0 or index > self.length:
            return False
            
        # Case 2: empty list 
        if self.length == 0:
            self.push(data)
        
        # Case 3: add to the beginning
        elif index == 0:
            new_node = Node(data)
            new_node.next = self.head
            self.head = new_node
        
        # Case 4: add to the end
        elif index == self.length:
            new_node = Node(data)
            self.tail.next = new_node
            self.tail = new_node
        
        # Case 5: add to the middle
        else:
            new_node = Node(data)
            current_node = self.head
            for _ in range(index-1):
                current_node = current_node.next
            new_node.next = current_node.next
            current_node.next = new_node
            
        self.length += 1
        return True

singlyLinkedList = SinglyLinkedList()
singlyLinkedList.push(5)  # Success
singlyLinkedList.push(10)  # Success
singlyLinkedList.push(15)  # Success
singlyLinkedList.push(20)  # Success
 
 
singlyLinkedList.insert(2, 12)  # True
singlyLinkedList.insert(100, 12) # False
singlyLinkedList.length         # 5
singlyLinkedList.head.val       # 5
singlyLinkedList.head.next.val   # 10
singlyLinkedList.head.next.next.val  # 12
singlyLinkedList.head.next.next.next.val # 15
singlyLinkedList.head.next.next.next.next.val # 20
 
singlyLinkedList.insert(5, 25) # True
singlyLinkedList.head.next.next.next.next.next.val # 25
singlyLinkedList.tail.val # 25