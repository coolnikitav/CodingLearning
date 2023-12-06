#include<iostream>
#include<vector>
#include<queue>

using namespace std;

class Solution {
    public:
        int fill_cups(vector<int>& amount) {
            int time = 0;
            
            priority_queue<int> pq;

            for (auto i : amount) {
                pq.push(i);
            }

            while (pq.top() != 0) {
                int a = pq.top();
                pq.pop();
                int b = pq.top();
                pq.pop();

                a--;
                b--;

                pq.push(a);
                pq.push(b);

                time++;
            }

            return time;
        }
};

int main() {
    Solution test = Solution();

    vector<int> amount1 = {1,4,2};
    
    cout << test.fill_cups(amount1) << endl;


    vector<int> amount2 = {5,4,4};
    
    cout << test.fill_cups(amount2) << endl;


    vector<int> amount3 = {5,0,0};
    
    cout << test.fill_cups(amount3) << endl;

}
