# divide and conquer
def number_factor(n):
    if n in (0,1,2):
        return 1
    elif n == 3:
        return 2
    else:
        sub_p1 = number_factor(n-1)
        sub_p2 = number_factor(n-3)
        sub_p3 = number_factor(n-4)
        return sub_p1 + sub_p2 + sub_p3
    
print(number_factor(5))

# dynamic programming
# top down
def number_factor(n, temp_dict):
    if n in (0,1,2):
        return 1
    elif n == 3:
        return 2
    else:
        if n not in temp_dict:
            sub_p1 = number_factor(n-1, temp_dict)
            sub_p2 = number_factor(n-3, temp_dict)
            sub_p3 = number_factor(n-4, temp_dict)
            temp_dict[n] = sub_p1 + sub_p2 + sub_p3
        return temp_dict[n]
print(number_factor(5, {}))

# bottom up
def number_factor(n):
    temp_arr = [1,1,1,2]
    for i in range(4, n+1):
        temp_arr.append(temp_arr[i-1] + temp_arr[i-3] + temp_arr[i-4])
    return temp_arr[n]

print(number_factor(5))
