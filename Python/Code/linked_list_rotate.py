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
        
    def rotate(self, number):
        if number < (-1 * self.length) or number > self.length:
            return None
        
        # Rotate(-1) = Rotate(4)
        if number < 0:
            number = number + 5

        for _ in range(number):
           head_node = self.head
           self.push(head_node.val)
           self.head = head_node.next
           head_node.next = None
          
        return self.head

singlyLinkedList = SinglyLinkedList()
singlyLinkedList.push(5)  # Success
singlyLinkedList.push(10)  # Success
singlyLinkedList.push(15)  # Success
singlyLinkedList.push(20)  # Success
singlyLinkedList.push(25)  # Success
 
singlyLinkedList.rotate(3)
 
singlyLinkedList.head.val  # 20
singlyLinkedList.head.next.val   # 25
singlyLinkedList.head.next.next.val  # 5
singlyLinkedList.head.next.next.next.val # 10
singlyLinkedList.head.next.next.next.next.val # 15
singlyLinkedList.tail.val # 15
singlyLinkedList.tail.next # None
 
 
singlyLinkedList = SinglyLinkedList()
singlyLinkedList.push(5)  # Success
singlyLinkedList.push(10)  # Success
singlyLinkedList.push(15)  # Success
singlyLinkedList.push(20)  # Success
singlyLinkedList.push(25)  # Success
 
singlyLinkedList.rotate(-1)
 
singlyLinkedList.head.val  # 25
singlyLinkedList.head.next.val   # 5
singlyLinkedList.head.next.next.val  # 10
singlyLinkedList.head.next.next.next.val # 15
singlyLinkedList.head.next.next.next.next.val # 20
singlyLinkedList.tail.val # 20
singlyLinkedList.tail.next # None