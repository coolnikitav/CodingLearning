my_dict = dict()
print(my_dict)
my_dict2 = {}
print(my_dict2)

eng_sp = dict(one='uno',two='dos',three='tres')
print(eng_sp)

eng_sp2 = {'one':'uno','two':'dos','three':'tres'}
print(eng_sp2)

eng_sp_list = [('one','uno'),('two','dos'),('three','tres')]
eng_sp3 = dict(eng_sp_list)
print(eng_sp3)

myDict = {'name':'Edy','age':26}
myDict['age'] = 27
myDict['address'] = 'London'

def traverseDict(dict):
    for key in dict:
        print(key, dict[key])

traverseDict((myDict))

def searchDict(dict, value):
    for key in dict:
        if dict[key] == value:
            return key,value
    return 'The value does not exist'

print(searchDict(myDict, 27))

myDict.clear()
print(myDict)

newDict = {'name':'Edy','age': 26, 'address':'London','education':'master'}
print(newDict)
newDict1 = newDict.copy()
print(newDict1)

newDict2 = {}.fromkeys([1,2,3],0)
print(newDict2)

print(newDict.get('address'))

print(newDict.items())

print(newDict.keys())

print(newDict.popitem())
print(newDict)

newDict['education'] = 'master'
print(newDict)

print(newDict.setdefault('name','added'))
print(newDict)

print(newDict.pop('name','not'))

print(newDict.values())

myDict = {'a':1,'b':2,'c':3}
newDict.update(myDict)
print(newDict)
newDict.update({'d':4})
print(newDict)

print(2 not in newDict.values())

print(len(newDict))

print(all(newDict))

print(any(newDict))

print(sorted(newDict))

import random

city_names = ['Paris', 'London', 'Rome', 'Berlin', 'Madrid']
city_temps = {city:random.randint(20,30) for city in city_names}
print(city_temps)

city_25 = {2*key:value for key,value in city_temps.items() if value > 25}
print(city_25)


def merge_dicts(dict1, dict2):
    # TODO
    merged = {}
    for item in dict1:
        #print(item,dict1[item])
        if item not in merged:
            merged[item] = dict1[item]
        else:
            merged[item] += dict1[item]
    for item in dict2:
        if item not in merged:
            merged[item] = dict2[item]
        else:
            merged[item] += dict2[item]
    print(merged)
    return merged


dict1 = {'a': 1, 'b': 2, 'c': 3}
dict2 = {'b': 3, 'c': 4, 'd': 5}

merge_dicts(dict1, dict2)

def max_value_key(my_dict):
    # TODO
    tempValue = 0
    for key,value in my_dict.items():
        print(key,value)
        print(tempValue)
        if value > tempValue:
            tempValue = value
            tempKey = key
    return key

my_dict = {'a': 5, 'b': 9, 'c': 2}
my_dict1 = {'b':9,'a':5,'c':2}
print(max_value_key(my_dict))

print(my_dict.get)

print(my_dict == my_dict1)