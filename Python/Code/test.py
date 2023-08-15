from array import *
import numpy as np

my_array = array('i',[1,2,3,4,5])
for num in my_array:
    print(num)

print(my_array[0])

my_array.append(6)

print(my_array)

my_array.insert(2, 69000)

print(my_array)

my_array1 = array('i', [10,11,12])
my_array.extend(my_array1)
print(my_array)

tempList = [20,21,22]
my_array.fromlist(tempList)
print(my_array)

my_array.remove(69000)
print(my_array)

my_array.pop()
print(my_array)

print(my_array.index(10))

my_array.reverse()
print(my_array)

print(my_array.buffer_info())

my_array.append(5)
print(my_array.count(5))


print(my_array.tolist())

print(my_array[5:8])

twoDArray = np.array([[11,15,10,6],[10,14,11,5],[12,17,12,8],[15,18,14,9]])
print(twoDArray)

newTwoDArray = np.insert(twoDArray, 0, [[1,2,3,4]], axis=0)
print(newTwoDArray)

newTwoDArray = np.append(twoDArray,[[1,2,3,4]],axis=0)
print(newTwoDArray)

integers = [1,2,2,3,4]
print(integers)

stringList = ['Milk','Cheese','Butter']
print(stringList)

mixedList = [1, 1.5, 'map']
print(mixedList)

nestedList = [1,2,4,5,[1.5,1.6],['test']]
print(nestedList)

emptyList = []
print(emptyList)

shoppingList = ['Milk', 'Cheese', 'Butter']
print(shoppingList[-1])

for i in range(len(shoppingList)):
    shoppingList[i] = shoppingList[i] + '+'
    print(shoppingList[i])

myList = [1,2,3,4,5,6,7]
print(myList)
myList[2] = 33
myList[4] = 55
print(myList)
myList.insert(0,11)
print(myList)
myList.append(58)
print(myList)
newList = [11,12,14,15]
myList.extend(newList)
print(myList)

myList = ['a', 'b', 'c', 'd', 'e', 'f']
myList[:3] = ['g','h']
print(myList)
myList.pop(0)
print(myList)
del myList[:1]
print(myList)
myList.remove('e')
print(myList)

my_list = [10,20,30,40,50,60,70,80,90]

target = 500
if target in my_list:
    print(f"{target} is in the list")
else:
    print(f"{target} is not in the list")

def linear_search(p_list, p_target):
    for i, value in enumerate(p_list):
        if value == p_target:
            return i
    return -1

print(linear_search(my_list, 50))

a = [1,2,3]
b = [4,5,6]
print(a+b)

a = [0,1]
a = a*4
print(a)

a = [0,1,2,3,4,5,6]
print(len(a))
print(max(a))
print(min(a))
print(sum(a)/len(a))

list1 = [2,4,3,1,5,7]
list1.sort()
print(list1)

new_list = [2*item for item in list1]
print(new_list)

language = 'python'
new_list = [letter for letter in language]
print(new_list)

list1 = [-1,10,-20,2,-90,60,45,20]
new_list = [2*number for number in list1 if number >= 0]
print(new_list)

sentence = 'My name is Elshad'
def is_consonant(letter):
    vowels = 'aeiouy'
    return letter.isalpha() and letter.lower() not in vowels

consonants = [i for i in sentence if is_consonant(i)]
print(consonants)

import numpy as np

myArray = np.array([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20])

def linear_search2(array, n):
    for num in array:
        if n == num:
            print(num)

linear_search2(myArray, 177)


def remove_duplicates(arr):
    # TODO
    i = 0
    while i < len(arr)-1:
        if arr[i] == arr[i+1]:
            arr.remove(arr[i+1])
        i+=1
    return arr

my_list3 = [1,1,2,2,3,4,5]
my_list3 = remove_duplicates(my_list3)
print(my_list3)

def pair_sum(myList, sum):
    # TODO
    hash_map = {}
    output = []
    for i in range(len(myList)):
        diff = sum - myList[i]
        if diff in hash_map:
            output.append(f'{myList[i]}+{diff}')
        else:
            hash_map[i] = diff
    print(hash_map)
    return output

my_list4 = [2,4,3,5,6,-2,4,7,8,9]
print(pair_sum(my_list4, 7))

def contains_duplicate(nums):
    # TODO
    temp = []
    for num in nums:
        if num in temp:
            return False
        else:
            temp.append(num)
    return True

mylist5 = [1,2,3,4]
print(contains_duplicate(mylist5))

my_dict = dict()
print(my_dict)