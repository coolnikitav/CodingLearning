#include<iostream>
#include<vector>
#include<queue>

using namespace std;

class Solution {
    public:
        vector<string> sort_people(vector<string>& names, vector<int>& heights) {
            priority_queue<pair<int,string>> pq;

            for (int i = 0; i < names.size(); i++) {
                pq.push({heights[i],names[i]});
            }

            for (int i = 0; i < names.size(); i++) {
                names[i] = pq.top().second;
                pq.pop();
            }

            return names;
        }

        template <typename T>
        void print_vector(const vector<T>& vec) {
            cout << "{";
            for (int i = 0; i < vec.size()-1; i++) {
                cout << vec[i] << ", ";
            }
            cout << vec[vec.size()-1]<< "}" << endl;
        }
};

int main() {
    Solution test = Solution();

    vector<string> names1 = {"Mary","John","Emma"};
    vector<int> heights1 = {180,165,170};
    test.print_vector(test.sort_people(names1, heights1));

    vector<string> names2 = {"Alice","Bob","Bob"};
    vector<int> heights2 = {155,185,150};
    test.print_vector(test.sort_people(names2, heights2));

    return 0;
}
