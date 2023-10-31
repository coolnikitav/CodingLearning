# Divide and Conquer
def find_min_operation(s1, s2, index1, index2):
  if index1 == len(s1):
    return len(s2) - index2
  if index2 == len(s2):
    return len(s1) - index1
  if s1[index1] == s2[index2]:
    return find_min_operation(s1, s2, index1+1, index2+1)
  else:
    delete_op = 1 + find_min_operation(s1, s2, index1, index2+1)
    insert_op = 1 + find_min_operation(s1, s2, index1+1, index2)
    replace_op = 1 + find_min_operation(s1, s2, index1+1, index2+1)
    return min(delete_op, insert_op, replace_op)

print(find_min_operation("table", "tbrles", 0, 0))

# Dynamic Programming
# Top Down
def convert_string(s1, s2, index1, index2, temp_dict):
  if index1 == len(s1):
    return len(s2)-index2
  if index2 == len(s2):
    return len(s1)-index1
  if s1[index1] == s2[index2]:
    return convert_string(s1, s2, index1+1, index2+1, temp_dict)
  else:
    dict_key = str(index1)+str(index2)
    if dict_key not in temp_dict:
      delete_op = 1 + convert_string(s1, s2, index1, index2+1, temp_dict)
      insert_op = 1 + convert_string(s1, s2, index1+1, index2, temp_dict)
      replace_op = 1 + convert_string(s1, s2, index1+1, index2+1, temp_dict)
      temp_dict[dict_key] = min(delete_op, insert_op, replace_op)
    return temp_dict[dict_key]

# Bottom Up
def findMinOperationBU(s1, s2, tempDict):
    for i1 in range(len(s1)+1):
        dictKey = str(i1)+'0'
        tempDict[dictKey] = i1
    for i2 in range(len(s2)+1):
        dictKey = '0'+str(i2)
        tempDict[dictKey] = i2
    
    for i1 in range(1,len(s1)+1):
        for i2 in range(1,len(s2)+1):
            if s1[i1-1] == s2[i2-1]:
                dictKey = str(i1)+str(i2)
                dictKey1 = str(i1-1)+str(i2-1)
                tempDict[dictKey] = tempDict[dictKey1]
            else:
                dictKey = str(i1)+str(i2)
                dictKeyD = str(i1-1)+str(i2)
                dictKeyI = str(i1)+str(i2-1)
                dictKeyR = str(i1-1)+str(i2-1)
                tempDict[dictKey] = 1 + min(tempDict[dictKeyD], min(tempDict[dictKeyI],tempDict[dictKeyR]))
    dictKey = str(len(s1))+str(len(s2))
    return tempDict[dictKey]
