class Node:
    def __init__(self, value):
        self.value = value
        self.next = None

class LinkedList:
    def __init__(self):
        self.head = None
        self.tail = None
        self.length = 0
    
    def __str__(self):
        temp_node = self.head
        result = ''
        while temp_node is not None:
            result += str(temp_node.value)
            if temp_node.next is not None:
                result += ' -> '
            temp_node = temp_node.next
        return result
    
    def append(self, value):
        new_node = Node(value)
        if self.head is None:
            self.head = new_node
            self.tail = new_node
        else:
            self.tail.next = new_node
            self.tail = new_node
        self.length += 1
        
    def reverse(self):
        # TODO
        current_node = self.head
        values = []
        while current_node:
            values.append(current_node.value)
            current_node = current_node.next
        print(values)
        current_node = self.head
        for i in range(self.length):
            current_node.value = values[-i-1]
            print(f"i: {i}")
            print(f"value: {values[-i]}")
            current_node = current_node.next

    def remove_duplicates(self):
        # TODO
        prev_node = self.head
        dups = set()
        current_node = prev_node.next
        while current_node:
            print(f"current: {current_node.value}, prev: {prev_node.value}, dups: {dups}")
            if current_node.value not in dups:
                dups.add(current_node.value)
            else:
                prev_node.next = current_node.next
                current_node.next = None
            print("here")
            prev_node = current_node
            current_node = current_node.next

linked_list = LinkedList()
linked_list.append(1)
linked_list.append(1)
linked_list.append(2)
linked_list.append(3)
linked_list.append(4)
linked_list.append(5)
linked_list.append(2)
linked_list.append(5)
linked_list.append(4)
print(linked_list)
linked_list.remove_duplicates()
print(linked_list)