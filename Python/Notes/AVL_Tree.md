AVL tree is a self-balancing BST where the difference between heights of left and right subtrees cannot be more than one for all nodes.

If at any time heights of left and right subtrees differ by more than one, then rebalancing is done to restor AVL property, this process is called rotation.

We need AVL trees to keep time complexity O(logN) because the tree rebalances when a new element is inserted.

Common operations on AVL trees:
- Creation of AVL trees
- Searching for a node
- Traversing all nodes
- Inserting a node
- Deleting a node
- Delete the entire tree

Creation of the tree, searching for a node, and traversing all nodes is the same as for BST.

When inserting a node, there are 2 cases: rotation is not required or is required (when the tree is unbalanced - the height difference is more than 1).

To determine which the insertion case: look at the disbalanced node, then look at its grandchild (select grandchild with greater height if there are 2).

# Inserting a node (left left condition)

We need to do a right rotation.

Algorithm:
```Python
rotateRigth(disbalancedNode):
    newRoot = disbalancedNode.leftChild
    disbalancedNode.leftChild = disbalancedNode.leftChild.rightChild
    newRoot.rightChild = disbalancedNode
    update height of disbalancedNode and newRoot
    return newRoot
```

Time complexity: O(1)

Space complexity: O(1)

