class Node:
    def __init__(self, data):
        self.data = data
        self.left = None
        self.right = None

class BST:
    def __init__(self):
        self.root = None
        
    def insert(self,data):
        new_node = Node(data)
        
        if not self.root:
            self.root = new_node
        else:
            self._insert(data, self.root)
        return self.root
            
    def _insert(self, data, root):
        if data < root.data:
            if not root.left:
                root.left = Node(data)
            else:
                self._insert(data, root.left)
        else:
            if not root.right:
                root.right = Node(data)
            else:
                self._insert(data, root. right)
                
    def find(self, data):
        return self._find(self.root, data)
    
    def _find(self, node, data):
        if not node:
            return None
        
        if node.data == data:
            return node
            
        left_node = self._find(node.left, data)
        right_node = self._find(node.right, data)
        return left_node if left_node else right_node

bsTree = BST() 
bsTree.insert(15)
bsTree.insert(20)
bsTree.insert(10)
bsTree.insert(12)
 
bsTree.find(20).data # 20
bsTree.find(20).right # None
bsTree.find(20).left # None
bsTree.find(100) # None