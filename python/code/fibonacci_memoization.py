def fib_memo(n, memo):
  if n == 1:
    return 0
  if n == 2:
    return 1
  if not n in memo:
    memo[n] = fib_memo(n-1, memo) + fib_memo(n-2, memo)
  return memo[n]

my_dict = {}
print(fib_memo(6, my_dict))
