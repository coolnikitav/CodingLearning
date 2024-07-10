class Solution {
public:
    long long getDescentPeriods(vector<int>& prices) {
        long long descent_periods = prices.size();
        int streak = 0;

        for (int i = 1; i < prices.size(); i++) {
            if (prices[i] - prices[i-1] == -1) {
                streak++;
                descent_periods += streak;
            } else {
                streak = 0;
            }
        }

        return descent_periods;
    }
};
