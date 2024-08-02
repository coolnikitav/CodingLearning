class Solution:
    def subsets(self, nums: List[int]) -> List[List[int]]:
        comb = [[]]

        def combinations(i: int, curr: List[int]):
            if i == len(nums):
                return

            if len(curr) > 0:
                comb.append(curr)
                combinations(i+1, curr)

            curr.append[nums[i]]
            comb.append(curr)
            combinations(i+1, curr)

        combinations(0, [])
        return comb

TypeError: 'builtin_function_or_method' object is not subscriptable
    ~~~~~~~~~~~^^^^^^^^^
    curr.append[nums[i]]
Line 13 in combinations (Solution.py)
    combinations(0, [])
Line 17 in subsets (Solution.py)
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ret = Solution().subsets(param_1)
Line 37 in _driver (Solution.py)
    _driver()
Line 48 in <module> (Solution.py)
