
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

def remove_duplicates(ll):
    # TODO
    dups = dict()
    prevNode = ll.head
    dups[prevNode.value] = 1
    currNode = prevNode.next
    while currNode:
        print("dups: ", dups)
        if currNode.value not in dups:
            dups[currNode.value] = 1
        else:
            nextNode = currNode.next
            prevNode.next = nextNode
            currNode.next = None
            ll.length -= 1
        print(currNode.value)
        currNode = nextNode
        prevNode = prevNode.next
    return ll

practiceList = LinkedList()
practiceList.append(5)
practiceList.append(5)
practiceList.append(6)
practiceList.append(0)
practiceList.append(7)
practiceList.append(0)
practiceList.append(6)
print(practiceList)
print(remove_duplicates(practiceList))