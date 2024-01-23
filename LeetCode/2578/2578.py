import heapq

def splitNum(num):
    """
    :type num: int
    :rtype: int
    """

    heap = []

    while num > 0:
        heapq.heappush(heap,-(num%10))
        num = num // 10

    num1 = 0
    num2 = 0

    def create_nums(heap,num,mult):
        nonlocal num1
        nonlocal num2
        if len(heap) == 0:
            return
        if num == "num1":
            num1 += -(heapq.heappop(heap))*mult
            return create_nums(heap,"num2",mult)
        if num == "num2":
            num2 += -(heapq.heappop(heap))*mult
            return create_nums(heap,"num1",10*mult)  
                
    create_nums(heap,"num1",1)
    return num1 + num2

print(splitNum(4325))  
print(splitNum(687)) 
print(splitNum(10)) 
print(splitNum(2222)) 
print(splitNum(222)) 
print(splitNum(222)) 
