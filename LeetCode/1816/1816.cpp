#include<iostream>

using namespace std;

class Solution {
    public:
        string truncate_sentence(string s, int k) {
            int space_count = 0;

            for (int i = 0; space_count < k; i++) {
                if (s[i] == ' ') {
                    space_count++;
                }

                if (space_count == k) {
                    return s.substr(0, i-1);
                }
            }

            return "";
        }
};

int main() {
    Solution test = Solution();

    string s1 = "Hello how are you Contestant";
    cout << test.truncate_sentence(s1,4) << endl;

    string s2 = "What is the solution to this problem";
    cout << test.truncate_sentence(s2,4) << endl;

    string s3 = "chopper is not a tanuki";
    cout << test.truncate_sentence(s3,5) << endl;

    return 0;
}
