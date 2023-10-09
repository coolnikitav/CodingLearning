class Node:
  def __init__(self, value):
    self.value = value
    self.next = None

class CSLinkedList:
  #def __init__(self, value):
  #  new_node = Node(value)
  #  new_node.next = new_node
  #  self.head = new_node
  #  self.tail = new_node
  #  self.length = 1

  def __init__(self):
    self.head = None
    self.tail = None
    self.length = 0

  def __str__(self):
    temp_node = self.head
    result = ""
    while temp_node:
      result += str(temp_node.value)
      temp_node = temp_node.next
      if temp_node == self.head:
        break
      result += ' -> '
    return result

  def append(self, value):
    new_node = Node(value)
    if self.length == 0:
      self.head = new_node
      self.tail = new_node
      new_node.next = new_node
    else:
      self.tail.next = new_node
      new_node.next = self.head
      self.tail = new_node
    self.length += 1

cslinkedlist = CSLinkedList()
cslinkedlist.append(10)
cslinkedlist.append(20)
print(cslinkedlist.head.value)
print(cslinkedlist.head.next.value)
print(cslinkedlist)
