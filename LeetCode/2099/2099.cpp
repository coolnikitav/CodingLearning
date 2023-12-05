#include<iostream>
#include<vector>
#include<queue>

using namespace std;

class Solution {
    public:
        vector<int> max_subsequence(vector<int>& nums, int k) {
            // Priority queue acts like a heap
            priority_queue<pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>>> pq;

            for (int i = 0; i < nums.size(); i++) {
                pq.push({nums[i], i});

                if (pq.size() > k) {
                    pq.pop();
                }
            }

            priority_queue<pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>>> temp;

            while (!pq.empty()) {
                temp.push({pq.top().second, pq.top().first});
                pq.pop();
            }

            vector<int> max_vector;

            while (!temp.empty()) {
                max_vector.push_back(temp.top().second);
                temp.pop();
            }

            return max_vector;
        }

        void print_vector(vector<int> nums) {
            cout << "{";
            for (int i = 0; i < nums.size()-1; i++) {
                cout << nums[i] << ", ";
            }
            cout << nums[nums.size()-1] << "}" << endl;
        }
};

int main() {
    Solution test = Solution();

    vector<int> vector1 = {2,1,3,3};
    test.print_vector(test.max_subsequence(vector1, 2));

    vector<int> vector2 = {-1,-2,3,4};
    test.print_vector(test.max_subsequence(vector2, 3));

    vector<int> vector3 = {3,4,3,3};
    test.print_vector(test.max_subsequence(vector3, 2));

    return 0;
}
