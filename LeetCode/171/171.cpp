#include<iostream>
#include<string>
#include<cmath>

using namespace std;

class Solution {
public:
    int titleToNumber(string columnTitle) {
        int num = 0;
        
        for (int i = 0; i < columnTitle.size(); i++) {
            num += (columnTitle[i] - 64) * pow(26, columnTitle.size()-1-i);
        }

        return num;
    }
};

int main() {
    Solution test = Solution();

    string columnTitle1 = "A";
    cout << test.titleToNumber(columnTitle1) << endl;

    string columnTitle2 = "AB";
    cout << test.titleToNumber(columnTitle2) << endl;

    string columnTitle3 = "ZY";
    cout << test.titleToNumber(columnTitle3) << endl;

    string columnTitle4 = "BAC";
    cout << test.titleToNumber(columnTitle4) << endl;

    return 0;
}
