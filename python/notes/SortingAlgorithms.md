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

Stable: yes

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

Stable: No

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

Stable: Yes

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

Stable: Yes

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

Stable: Yes

When to use merge sort?
- When you need stable sort
- When average expected time is O(NlogN)

When to avoid merge sort?
- When space is a concern

# Quick sort
QuickSort is a sorting algorithm that works by selecting a pivot element from the array and rearranging the elements so that all smaller elements are on the left and larger elements are on the right. This creates two sub-arrays. The same process is then applied recursively to these sub-arrays until they're sorted. The pivot's final position is its correct place in the sorted array.
```Python
def swap(my_list, index1, index2):
    my_list[index1], my_list[index2] = my_list[index2], my_list[index1]

def pivot(my_list, pivot_index, end_index):
    swap_index = pivot_index
    for i in range(pivot_index+1, end_index+1):
        if my_list[i] < my_list[pivot_index]:
            swap_index += 1
            swap(my_list, swap_index, i)
    swap(my_list, pivot_index, swap_index)
    return swap_index

def quickSort_helper(my_list, left, right):
    if left < right:
        pivot_index = pivot(my_list, left, right)
        quickSort_helper(my_list, left, pivot_index-1)
        quickSort_helper(my_list, pivot_index+1, right)
    return my_list

def quickSort(my_list):
    return quickSort_helper(my_list, 0, len(my_list)-1)

my_list = [3,5,6,0,2,1,4]
print(quickSort(my_list))
```
Time complexity: O(NlogN)

Space complexity: O(1)

Stable: No

# Heap sort
- Step 1: Insert data to binary heap tree
- Step 2: Extract data from binary heap
- It is best suited with array, it does not work with linked list
```Python
def heapify(customList, n, i):
    smallest = i
    l = 2*i + 1
    r = 2*i + 2
    if l < n and customList[l] < customList[smallest]:
        smallest = l
    
    if r < n and customList[r] < customList[smallest]:
        smallest = r

    if smallest != i:
        customList[i], customList[smallest] = customList[smallest], customList[i]
        heapify(customList, n, smallest)

def heapSort(customList):
    n = len(customList)
    for i in range(int(n/2)-1, -1, -1):
        heapify(customList, n, i)
    
    for i in range(n-1, 0, -1):
        customList[i], customList[0] = customList[0], customList[i]
        heapify(customList, i, 0)
    customList.reverse()

cList = [2,1,7,6,5,3, 4, 9,8]
heapSort(cList)
print(cList)
```
Time complexity: O(NlogN)

Space complexity: O(1)

Stable: No