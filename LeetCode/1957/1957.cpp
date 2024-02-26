#include <iostream>
#include <string>

using namespace std;

class Solution {
public:
    string makeFancyString(string s) {
        int idx = size(s)-1;
        int count = 1;
        while (idx > -1) {  // cover the case where letters repeat in the beginning
            if (idx > 0 && s[idx-1] == s[idx]) {
                count++;
            } else {
                if (count > 2) {
                    s.erase(s.begin()+idx+2, s.begin()+idx+count);
                }
                count = 1;
            }
            idx--;
        }
        return s;
    }
};

int main(){
    Solution test = Solution();

    cout << test.makeFancyString("leeetcode") << endl;
    cout << test.makeFancyString("aaabaaaa") << endl;
    cout << test.makeFancyString("aab") << endl;
    cout << test.makeFancyString("aabaabaabaa") << endl;

    return -1;
}
