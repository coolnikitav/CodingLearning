class Solution:
    def maxProfit(self, prices: List[int], fee: int) -> int:
        # Recursive
        # def max_profit_recursive(day,open_position):
        #     if day >= len(prices):
        #         return 0

        #     if not open_position:
        #         buy = max_profit_recursive(day+1,True)-prices[day]
        #         skip = max_profit_recursive(day+1,False)
        #         return max(buy,skip)
        #     if open_position:
        #         sell = max_profit_recursive(day+1,False)+prices[day]-fee
        #         skip = max_profit_recursive(day+1,True)
        #         return max(sell,skip)
            
        # return max_profit_recursive(0,False)

        # Recursive with memoization
        # memo = {}
        # def max_profit_recursive(day,open_position):
        #     if day >= len(prices):
        #         return 0
            
        #     if (day,open_position) not in memo:
        #         if not open_position:
        #             buy = max_profit_recursive(day+1,True)-prices[day]
        #             skip = max_profit_recursive(day+1,False)
        #             memo[(day,open_position)] = max(buy,skip)
        #         if open_position:
        #             sell = max_profit_recursive(day+1,False)+prices[day]-fee
        #             skip = max_profit_recursive(day+1,True)
        #             memo[(day,open_position)] = max(sell,skip)
            
        #     return memo[(day,open_position)]
        # return max_profit_recursive(0,False)

        # DP
        #      F T
        #      0 1
        #      ---
        # 1 0| 0 0
        # 3 1| 0 0
        # 2 2| 0 0
        # 8 3| 0 0
        # 4 4| 0 0
        # 9 5| 0 0
        #   6| 0 0
        grid = [[0 for _ in range(2)] for _ in range(len(prices)+1)]

        for row in range(len(prices)-1,-1,-1):
            grid[row][0] = max(grid[row+1][1]-prices[row],grid[row+1][0])
            grid[row][1] = max(grid[row+1][0]+prices[row]-fee,grid[row+1][1])
        
        return grid[0][0]