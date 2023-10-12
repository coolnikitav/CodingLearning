A trie is a tree-based data structure that organizes information in a hierarchy.

Properties:
- It is typically used to store or search strings in a space and time efficient way.
- Any node in trie can store non repetitive multiple characters
- Every node stores link of the next character of the string
- Every node keeps track of 'end of string'
  
![image](https://github.com/coolnikitav/CodingLearning/assets/30304422/afd74e26-1e78-4045-8080-a56244089acc)

Why we need trie (examples)?
- Spelling checker
- Auto completion

Common operations on Trie
- Creation of Trie
- Insertion of Trie
- Search for a string in Trie
- Deletion from Trie

# Creation of Trie
```Python
class TrieNode:
    def __init__(self):
        self.children = {}
        self.endOfString = False
    
class Trie:
    def __init__(self):
        self.root = TrieNode()

newTrie = Trie()
```
Time complexity: O(1)

Space complexity: O(1)

# Insert a string in Trie
4 cases:
- A Trie is Blank
- New strins's prefix is common to another strings prefix
- New string's prefix is already present as complete string
- String to be inserted is already presented in Trie
```Python
def insertString(self, word):
        current = self.root
        for ch in word:
            node = current.children.get(ch)
            if node == None:
                node = TrieNode()
                current.children.update({ch:node})
            current = node
        current.endOfString = True
        print("Successfully inserted")
```
Time complexity: O(n)

Space complexity: O(n)

# Search for a string in a Trie
4 cases:
- String does not exist in Trie
- String exists in Trie
- String is a prefix of another string, but it does not exist in a Trie
```Python
def searchString(self, word):
        currentNode = self.root
        for ch in word:
            node = currentNode.children.get(ch)
            if node == None:
                return False
            currentNode = node

        if currentNode.endOfString == True:
            return True
        else:
            return False

newTrie = Trie()

newTrie.insertString("App")
newTrie.insertString("Appl")
print(newTrie.searchString("App"))
print(newTrie.searchString("Ap"))
```
Time complexity: O(n)

Space complexity: O(n)

# Delete a string from Trie
4 cases:
- Some other prefix of string is same as the one that we want to delete.
- The string is a prefix of another string.
- Other string is a prefix of this string.
- Not any node depends on this string.
```Python
def deleteString(root, word, index):
    ch = word[index]
    currentNode = root.children.get(ch)
    canThisNodeBeDeleted = False

    if len(currentNode.children) > 1:
        deleteString(currentNode, word, index+1)
        return False
    
    if index == len(word)-1:
        if len(currentNode.children) >= 1:
            currentNode.endOfString = False
            return False
        else:
            root.children.pop(ch)
            return True
        
    if currentNode.endOfString == True:
        deleteString(currentNode, word, index+1)
        return False
    
    canThisNodeBeDeleted = deleteString(currentNode, word, index + 1)
    if canThisNodeBeDeleted == True:
        root.children.pop(ch)
        return True
    else:
        return False

deleteString(newTrie.root, "App", 0)
print(newTrie.searchString("App"))
```
