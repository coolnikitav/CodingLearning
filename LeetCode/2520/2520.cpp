#include <iostream>

using namespace std;

class Solution {
public:
    int countDigits(int num) {
        int dividend = num;
        int divisors = 0;
        while (num > 0) {
            if (dividend % (num%10) == 0) {
                divisors++;
            }
            num /= 10;
        }
        return divisors;
    }
};

int main() {
    Solution test = Solution();

    cout << test.countDigits(7) << endl;
    cout << test.countDigits(121) << endl;
    cout << test.countDigits(1248) << endl;

    return -1;
}
