#include<iostream>

using namespace std;

class Solution {
    public:
        int max_depth(string s) {
            int max_depth = 0;
            int current_depth = 0;

            for (int i = 0; i < s.size(); i++) {
                if (s[i] == '(') {
                    current_depth++;
                    max_depth = max(max_depth, current_depth);
                } else if (s[i] == ')') {
                    current_depth--;
                }
            }

            return max_depth;
        }
};

int main() {
    Solution test = Solution();

    string s1 = "(1+(2*3)+((8)/4))+1";
    cout << test.max_depth(s1) << endl;

    string s2 = "(1)+((2))+(((3)))";
    cout << test.max_depth(s2) << endl;

    return 0;
}