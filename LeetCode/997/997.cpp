#include<iostream>
#include<vector>
#include<unordered_map>

using namespace std;

class Solution {
    public:
        int find_judge(int n, vector<vector<int>>& trust) {
            unordered_map<int,int> trustee;
            unordered_map<int,int> trusted;
            
            for (int i = 0; i < trust.size(); i++) {
                trustee[trust[i][0]]++;
                trusted[trust[i][1]]++;
            }
            
            for (int i = 1; i <= n; i++) {
                if (trustee.find(i) == trustee.end() && trusted[i] == n-1) {
                    return i;
                }
            }

            return -1;
        }
};

int main() {
    Solution test = Solution();

    vector<vector<int>> trust1 = {{1,2}};
    cout << test.find_judge(2, trust1) << endl;

    vector<vector<int>> trust2 = {{1,3},{2,3}};
    cout << test.find_judge(3, trust2) << endl;

    vector<vector<int>> trust3 = {{1,3},{2,3},{3,1}};
    cout << test.find_judge(3, trust3) << endl;

    vector<vector<int>> trust4 = {{1,3},{1,4},{2,3},{2,4},{4,3}};
    cout << test.find_judge(4, trust4) << endl;

    vector<vector<int>> trust5 = {{1,2},{2,3}};
    cout << test.find_judge(3, trust5) << endl;

    return 0;
}
