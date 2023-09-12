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