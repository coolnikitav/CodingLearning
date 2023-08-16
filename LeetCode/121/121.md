class Solution(object):
    def maxProfit(self, prices):
        """
        :type prices: List[int]
        :rtype: int
        """
        profit = 0

        low = prices[0]

        for price in prices:
            if price < low:
                low = price
            else:
                profit = max(profit, price-low)
            
        return profit
