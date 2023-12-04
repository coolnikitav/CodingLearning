#include<iostream>
#include<vector>

using namespace std;

class Solution {
public:
    int maximumWealth(vector<vector<int>>& accounts) {
        int max_wealth = 0;

        for (int customer = 0; customer < accounts.size(); customer++) {
            int customer_wealth = 0;
            for (int bank = 0; bank < accounts[customer].size(); bank++) {
                customer_wealth += accounts[customer][bank];
            }

            max_wealth = max(max_wealth, customer_wealth);
        }

        return max_wealth;
    }
};

int main() {
    Solution test = Solution();

    vector<vector<int>> accounts1 = {{1,2,3},{3,2,1}};
    cout << test.maximumWealth(accounts1) << endl;

    vector<vector<int>> accounts2 = {{1,5},{7,3},{3,5}};
    cout << test.maximumWealth(accounts2) << endl;

    vector<vector<int>> accounts3 = {{2,8,7},{7,1,3},{1,9,5}};
    cout << test.maximumWealth(accounts3) << endl;
    return 0;
}
