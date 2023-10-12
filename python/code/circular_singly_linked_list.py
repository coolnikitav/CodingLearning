class Node:
  def __init__(self, value):
    self.value = value
    self.next = None

  def __str__(self):
    return str(self.value)

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

  def prepend(self, value):
    new_node = Node(value)
    if self.length == 0:
      self.head = new_node
      self.tail = new_node
      new_node.next = new_node
    else:
      new_node.next = self.head
      self.head = new_node
      self.tail.next = new_node
    self.length += 1

  def insert(self, index, value):
    new_node = Node(value)
    if index > self.length or index < 0:
      raise Exception("Index out of range")
    if index == 0:
      if self.length == 0:
        self.head = new_node
        self.tail = new_node
        new_node.next = new_node
      else:
        new_node.next = self.head
        self.head = new_node
        self.tail.next = new_node
    elif index == self.length:
      self.tail.next = new_node
      new_node.next = self.head
      self.tail = new_node
    else:
      temp_node = self.head
      for _ in range(index-1):
        temp_node = temp_node.next
      new_node.next = temp_node.next
      temp_node.next = new_node
    self.length += 1

  def traverse(self):
    current = self.head
    while current:
      print(current.value)
      current = current.next
      if current == self.head:
        break

  def search(self, target):
    current = self.head
    while current:
      if current.value == target:
        return True
      current = current.next
      if current = self.head:
        break
    return False

  def get(self, index):
    if index == -1:
      return self.tail
    if index < -1 or index >= self.length:
      return None
    current = self.head
    for _ in range(index):
      current = current.next
    return current

  def set_value(self, index, value):
    temp = self.get(index)
    if temp:
      temp.value = value
      return True
    return False

  def pop_first(self):
    popped_node = self.head
    if self.length == 0:
      return None
    if self.length == 1:
      self.head = None
      self.tail = None
    else:
      self.head = self.head.next
      self.tail.next = self.head
      popped_node.next = None
    self.length -= 1
    return popped_node

  def pop(self):
    if self.length == 0:
      return None
    popped_node = self.tail
    if self.length == 1:
      self.head = self.tail = None
    else:
      temp = self.head
      while temp.next is not self.tail:
        temp = temp.next
      temp.next = self.head
      self.tail = temp
      popped_node.next = None
    self.length -= 1
    return popped_node

  def remove(self, index):
    if index < 0: or index >= self.length:
      return None
    elif index == 0:
      return self.pop_first()
    elif index == self.length-1:
      return self.pop()
    prev_node = self.get(index-1)
    popped_node = prev_node.next
    prev_node.next = popped_node.next
    popped_node.next = None
    self.length -= 1
    return popped_node

  def delete_all(self):
    if self.length == 0:
      return
    self.tail.next = None
    self.head = None
    self.tail = None
    self.length = 0

cslinkedlist = CSLinkedList()
cslinkedlist.append(10)
cslinkedlist.append(20)
cslinkedlist.append(70)
cslinkedlist.append(80)
cslinkedlist.prepend(5)
cslinkedlist.prepend(1)
cslinkedlist.insert(0, 30)
cslinkedlist.insert(2, 50)
cslinkedlist.insert(100, 100)
print(cslinkedlist.head.value)
print(cslinkedlist.head.next.value)
print(cslinkedlist)
print(cslinkedlist.traverse())
print(cslinkedlist.search(50))
print(cslinkedlist.search(60))
print(cslinkedlist.get(2))
print(cslinkedlist.get(-1))
print(cslinkedlist.set(-1, 100))
print(cslinkedlist.set(2, 11))
print(cslinkedlist)
print(cslinkedlist.pop_first())
print(cslinkedlist.pop())
print(cslinkedlist)
print(cslinkedlist.remove(1))
cslinkedlist.delete(all)
print(cslinkedlist)
