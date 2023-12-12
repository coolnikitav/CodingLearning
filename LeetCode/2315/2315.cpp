#include<iostream>

using namespace std;

class Solution {
    public:
        int count_asterisks(string s) {
            int bar_count = 0;
            int asterisk_count = 0;

            for (int i = 0; i < s.size(); i++) {
                if (s[i] == '|') {
                    bar_count++;
                } else if (s[i] == '*') {
                    if (bar_count % 2 == 0) {
                        asterisk_count++;
                    }
                }
            }

            return asterisk_count;
        }
};

int main() {
    Solution test = Solution();

    string s1 = "l|*e*et|c**o|*de|";
    cout << test.count_asterisks(s1) << endl;

    string s2 = "iamprogrammer";
    cout << test.count_asterisks(s2) << endl;

    string s3 = "yo|uar|e**|b|e***au|tifu|l";
    cout << test.count_asterisks(s3) << endl;

    return 0;
}
