# What is hashing?
Hashing is a method of sorting and indexing data. The idea behind hashing is to allow large amounts of data to be indexed using keys commonly created by formulas.

# Why hashing?
It is time efficient in case of Search operation:
- Sorted Array/Python list: O(logN)
- Linked list: O(N)
- Balanced Tree: O(logN)
- Hashing O(1)/O(N)

# Hashing terminology
Hash function: function that can be used to map of arbitrary size to data of fixed size.
Key: input data by a user
Hash value: a value that is returned by Hash function
Hash table: a data structure which implements an associative array abstract data type, a structure that can map keys to values
Collision: a collision occures when two different keys to a hash function produce the same output.

# Hash functions
Mod function:
```Python
def mod(number, cellNumber):
    return number % cellNumber
```
ASCII function:
```Python
def modASCII(string, cellNumber):
    total = 0
    for i in string:
        total += ord(i)    # ord() converts to ASCII value
    return total % cellNumber
```
Properties of good Hash functions:
- Distributes hash values uniformly across hash tables
- It has to use all the input data
