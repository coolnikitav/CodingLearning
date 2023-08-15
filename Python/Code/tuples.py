newTuple = ('a','b','c','d','e')
print(newTuple)

newTuple1 = ('a')
print(newTuple1)

newTuple2 = ('a',)
print(newTuple2)

newTuple = tuple('abcde')
print(newTuple)

newTuple = ('a','b','c','d','e')
print(newTuple[-1])
print(newTuple[1:3])

for i in newTuple:
    print(i)

for i in range(len(newTuple)):
    print(newTuple[i])

print('a' in newTuple)
print('f' in newTuple)

print(newTuple.index('a'))
#print(newTuple.index('f'))

def searchTuple(p_tuple, element):
    for i in range(0, len(p_tuple)):
        if p_tuple[i] == element:
            return f"The {element} is found at {i} index"
    return 'The element is not found'

print(searchTuple(newTuple, 'b'))
print(searchTuple(newTuple, 'f'))

myTuple = (1,4,3,2,5,2)
myTuple1 = (1,2,6,9,8,7)
print(myTuple+myTuple1)
print(myTuple*3)
print(4 in myTuple)
print(myTuple.count(2))
print(myTuple.index(2))
print(len(myTuple))
print(max(myTuple))
print(min(myTuple))
print(tuple([1,2,3,4]))

input_tuple = ('Hello', 'World', 'from', 'Python')

def concatenate_strings(input_tuple):
    # TODO
    output = ''
    for i in input_tuple:
        print(i)

concatenate_strings(input_tuple)

print('a'.join(input_tuple))

def common_elements(tuple1, tuple2):
    # TODO
    return tuple(set(tuple1) ^ set(tuple2))

tuple1 = (1, 2, 3, 4, 5)
tuple2 = (4, 5, 6, 7, 8)
output_tuple = common_elements(tuple1, tuple2)
print(output_tuple)  # Expected output: (4, 5)