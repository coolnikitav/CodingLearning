# What is sorting?

By definition, sorting refers to arranging data in a particular format: either ascending or descending.

Practical use of sorting:
- Microsoft excel: built in functionality to sort data
- Online shopping: price, data, review...

# Types of sorting
Space used:
- In place sorting: does not require any extra space for sorting (bubble sort)
- Out place sorting: requires extra spacing for sorting (merge sort)

Stability:
- Stable sorting: if there are duplicates, they remain in the same order (insertion sort)
- Unstable sorting: if there are duplicates, they may not remain in the same order (quick sort)

# Sorting terminology

Increasing order:
- Successive element is greater than the previous one

Decreasing order:
- Successive element is less than the previous one

Non increasing order:
- Successive element is less than or equal to its previous element in the sequence

Non decreasing order:
- Successive element is greater than or equal to its previous element in the sequence

# Sorting algorithms:
Bubble sort
Selection sort
Insertion sort
Bucket sort
Merge sort
Quick sort
Heap sort

Which one to select?
- Stability
- Space efficient
- Time efficient

# Bubble sort
- Also referred to as sinking sort.
- We repeatedly compare each pair of adjacent items and swap them if they are in the wrong order.
```Python
def bubbleSort(customList):
    for i in range(len(customList)-1):
        for j in range(len(customList)-i-1):
            if customList[j] > customList[j+1]:
                customList[j], customList[j+1] = customList[j+1], customList[j]
    print(customList)

cList = [2,1,7,6,5,3,9,8]
bubbleSort(cList)
```
Time complexity: O(N^2)

Space complexity: O(1)

When to use Bubble sort?
- When the input is already sorted
- Space is a concern
- Easy to implement

When to avoid Bubble sort?
- Average time complexity

# Selection sort
- Repeatedly find the minimum element and move it to the sorted part of array to make unsorted part sorted
```Python
def selectionSort(customList):
    for i in range(len(customList)):
        min_index = i
        for j in range(i+1, len(customList)):
            if customList[min_index] > customList[j]:
                min_index = j
        customList[i], customList[min_index] = customList[min_index], customList[i]
    print(customList)

cList = [2,1,7,6,5,3,9,8]
selectionSort(cList)
```
Time complexity: O(N^2)

Space complexity: O(1)

When to use selection sort?
- When we have insufficient memory
- Easy to implement

When to avoid selection sort?
- When time is a concern

# Insertion sort
- Divide the given array into two parts
- Take first element from unsorted array and find its correct position in sorted array
- Repeat until unsorted array is sorted
```Python
def insertionSort(customList):
    for i in range(1, len(customList)):
        key = customList[i]
        j = i-1
        while j >= 0 and key < customList[j]:
            customList[j+1] = customList[j]
            j -= 1
        customList[j+1] = key
    print(customList)

cList = [2,1,7,6,5,3,9,8]
insertionSort(cList)
```
Time complexity: O(N^2)

Space complexity: O(1)

When to use insertion sort?
- When we have insufficient memory
- Easy to implement
- When we have continuous inflow of numbers and we want to keep them sorted

When to avoid insertion sort?
- When time is a concern

# Bucket sort
- Create buckets and distribute elements of array into buckets
- Sort buckets individually
- Merge buckets after sorting
- Number of buckets = round(sqrt(number of elements))
- Appropriate bucket = ceil(value * number of buckets/maxValue)
- Sort all buckets (using any sorting algorithm)

```Python
def bucketSort(customList):
    numberOfBuckets = round(math.sqrt(len(customList)))
    maxValue = max(customList)
    arr = []

    for i in range(numberOfBuckets):
        arr.append([])
    for j in customList:
        index_b = math.ceil(j*numberOfBuckets/maxValue)
        arr[index_b-1].append(j)

    for i in range(numberOfBuckets):
        arr[i] = insertionSort(arr[i])
    
    k = 0
    for i in range(numberOfBuckets):
        for j in range(len(arr[i])):
            customList[k] = arr[i][j]
            k += 1
    return customList

cList = [2,1,7,6,5,3,9,8]
bucketSort(cList)
```
Time complexity: O(N^2)

Space complexity: O(N)

When to use bucket sort? 
- When input uniformly distributed over range

When to avoid bucket sort?
- When space is a concern

# Merge sort
- Divide and conquer algorithm
- Divide the input array in two halves and we keep halving recursively until they become too small that cannot be broken further
- Merge halves by sorting them
```Python
def merge(customList, l, m, r):
    n1 = m - l + 1
    n2 = r - m

    L = [0] * (n1)
    R = [0] * (n2)

    for i in range(0, n1):
        L[i] = customList[l+i]
    
    for j in range(0, n2):
        R[j] = customList[m+1+j]
    
    i = 0 
    j = 0
    k = l
    while i < n1 and j < n2:
        if L[i] <= R[j]:
            customList[k] = L[i]
            i += 1
        else:
            customList[k] = R[j]
            j += 1
        k += 1
    while i < n1:
        customList[k] = L[i]
        i += 1
        k += 1
    
    while j < n2:
        customList[k] = R[j]
        j += 1
        k += 1

def mergeSort(customList, l, r):
    if l < r:
        m = (l+(r-1))//2
        mergeSort(customList, l, m)
        mergeSort(customList, m+1, r)
        merge(customList, l, m, r)
    return customList

cList = [2,1,7,6,5,3, 4, 9,8]
mergeSort(cList, 0, 8)
```
Time complexity: O(NlogN)

Space complexity: O(N)

When to use merge sort?
- When you need stable sort
- When average expected time is O(NlogN)

When to avoid merge sort?
- When space is a concern