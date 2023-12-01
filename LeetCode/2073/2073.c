#include<iostream>
#include<vector>

using namespace std;

class Solution {
public:
    int timeRequiredToBuy(vector<int>& tickets, int k) {
        int time = 0;
        int curr_index = 0;

        while (tickets[k] > 0) {
            if (tickets[curr_index] > 0) {
                tickets[curr_index]--;
                time++;
            }

            curr_index++;

            if (curr_index == tickets.size()) {
                curr_index = 0;
            }
        }

        return time;
    }
};

int main() {
    Solution test = Solution();

    vector<int> tickets1 = {2,3,2};
    int k1 = 2;

    cout << test.timeRequiredToBuy(tickets1, k1) << endl;

    vector<int> tickets2 = {5,1,1,1};
    int k2 = 0;

    cout << test.timeRequiredToBuy(tickets2, k2) << endl;
    return 0;
}
