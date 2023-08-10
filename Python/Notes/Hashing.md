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

# Collision Resolution Techniques
Direct chaining: implement the buckets as linked list. Colliding elements are stored in this lists

Open addressing: colliding elements are stored in other vacant buckets. During storage and lookup these are found through so called probing.
- Linear probing: It places new key into closest following empty cell
- Quadratic probing: Adding arbitrary quadratic polynomial ot the index until an empty cell is found. (index + 1^2 + 2^2...)
- Double hashing: interval between probes is computed by another hash function.

# What to do if a hash table is full

Direct chaining: the situation will never arise

Open addressing: Create 2x size of current hash table and recall hashing for current keys.

# Pros and cons of collision resolution techniques
Direct chaining
- Hash table never gets full
- Huge linked list causes performance leaks (Time complexity for search operation becomes O(N)

Open addressing
- Easy implementation
- When hash table is full, creation of new hash table affects performance (Time complexity for search operation becomes O(N)).

If the input size is known we always use "Open addressing".
If we perform deletion operation frequently we use "Direct chaining".

# Practical use of hashing
Password verification: puts password through a hash function. Look up instantly. Helps with security breaches because hacker would only see the hash values.

File system: file path is mapped to physical location on disk.

# Pros and cons of hashing

On average, insertion/deletion/search operations take O(1) time.

When hash function is not good enough, insertion/deletion/search operations take O(N) time.
