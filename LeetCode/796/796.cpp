#include<iostream>
#include<string>

using namespace std;

class Solution {
    public:
        bool rotate_string(string s, string goal) {
            if (s.size() != goal.size()) {
                return false;
            }

            string concatenated = goal + goal;

            return concatenated.find(s) != string::npos;
        }
};

int main() {
    Solution test = Solution();

    string s1 = "abcde";
    string goal1 = "cdeab";
    cout << test.rotate_string(s1,goal1) << endl;

    string s2 = "abcde";
    string goal2 = "abced";
    cout << test.rotate_string(s2,goal2) << endl;

    string s3 = "kifcqeiqoh";
    string goal3 = "ayyrddojpq";
    cout << test.rotate_string(s3,goal3) << endl;

    string s4 = "aabcde";
    string goal4 = "baaced";
    cout << test.rotate_string(s4,goal4) << endl;

    string s5 = "aaaa";
    string goal5 = "aaa";
    cout << test.rotate_string(s5,goal5) << endl;

    return 0;
}
