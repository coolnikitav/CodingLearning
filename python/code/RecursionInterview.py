# def sumOfDigits(num):
#     assert num >= 0 and isinstance(num, int), "Please enter an integer"
#     if num == 0:
#         return 0
#     return num % 10 + sumOfDigits(num//10)

# print(sumOfDigits(234))

# def powerOfNum(base, exp):
#     assert isinstance(exp, int), "Please enter non-negative integer exponent"
#     if exp == 0:
#         return 1
#     elif exp < 0:
#         return 1/base * powerOfNum(base, exp+1)
#     return base * powerOfNum(base, exp-1)

# print(powerOfNum(2, -5))

# def GCD(num1, num2):
#     assert int(num1) == num1 and int(num2) == num2, 'The numbers must be intergers'
#     if num1 < 0:
#         num1 = -1 * num1
#     if num2 < 0:
#         num2 = -1 * num2
#     if num2 == 0:
#         return num1
#     return GCD(num2, num1%num2)

# print(GCD(51, 34))

def decToBin(num):
    assert int(num) == num, "The number must be an integer"
    if num == 1 or num == 0:
        return num
    return num%2 + 10*decToBin(int(num/2))

print(decToBin(-285))