#include<iostream>
#include<vector>
#include<string>

using namespace std;

class Solution {
    public:
        bool determine_if_num(string& s) {
            for (int i = 0; i < s.size(); i++) {
                if (!isdigit(s[i])) {
                    return false;
                }
            }
            return true;
        }

        int maximum_value(vector<string>& strs) {
            int max_value = 0;

            for (int i = 0; i < strs.size(); i++) {
                if (determine_if_num(strs[i])) {
                    max_value = max(max_value, stoi(strs[i]));
                } else {
                    int word_length = strs[i].size();
                    max_value = max(max_value, word_length);
                }
            }

            return max_value;
        }
};

int main() {
    Solution test = Solution();

    vector<string> strs1 = {"alic3","bob","3","4","00000"};
    cout << test.maximum_value(strs1) << endl;

    vector<string> strs2 = {"1","01","001","0001"};
    cout << test.maximum_value(strs2) << endl;

    return 0;
}
