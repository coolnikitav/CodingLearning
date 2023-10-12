# Linear search
Simply searches elements one by one

Time complexity: O(N)

Space complexity: O(1)

# Binary search
- Binary search is faster than linear search
- Half of the remaining elements can be eliminated at a time, instead of eliminating them one by one
- Binary search only works for sorted arrays

Algorithm:
- Create a function with two parameters which are a sorted array and a value
- Create two pointers: a left pointer at the start of the array and a right pointer at the end of the array.
- Based on left and right pointers calculate middle pointer
- While middle is not equal to the value and start <= end loop:
    - if the middle is greater than the value move the right pointer down
    - if the middle is less than the value move the left pointer up
- If the value is never found, return -1

Time complexity:
- Worst and average case: O(logN)
- Best case: O(1)