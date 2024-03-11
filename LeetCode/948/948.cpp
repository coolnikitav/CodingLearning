#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

class Solution {
public:
    int bagOfTokensScore(vector<int>& tokens, int power) {
        // Approach: imagine an equation: power + n tokens = m tokens
        // We want to maximize m and minimize n to get the max score
        // Thus, we need to sort tokens and then keep inserting them into the equation
        sort(tokens.begin(), tokens.end());
        int beg = 0;
        int end = size(tokens)-1;
        
        int large_power = power;  // total value on the left side
        int small_power = 0;      // total value on the right side

        int large_tokens = 0;     // num of token added to the left side
        int small_tokens = 0;     // num of token added to the right side

        int max_score = 0;

        while (beg <= end) {
            if(large_power-small_power >= tokens[beg] || small_tokens - large_tokens >= 1) {  // make sure we have a legal move
                if (small_power <= large_power) {
                small_power += tokens[beg];
                small_tokens++;
                beg++;
                } else {
                    large_power += tokens[end];
                    large_tokens++;
                    end--;
                }
            } else {
                break;
            }            
        }
        
        if (small_power > large_power) {
            max_score = small_tokens - large_tokens - 1;  // we shouldntve added the last token to the right side. Ex: tokens = [200,100], power = 150
        } else {
            max_score = small_tokens - large_tokens;
        }
        return max_score;
    }
};

int main() {
    Solution test = Solution();

    vector<int> v1 = {100};
    cout << test.bagOfTokensScore(v1, 50) << endl;

    vector<int> v2 = {200,100};
    cout << test.bagOfTokensScore(v2, 150) << endl;

    vector<int> v3 = {100,200,300,400};
    cout << test.bagOfTokensScore(v3, 200) << endl;

    vector<int> v4 = {71,55,82};
    cout << test.bagOfTokensScore(v4, 54) << endl;
    return -1;
}
