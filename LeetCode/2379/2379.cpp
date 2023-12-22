#include<iostream>

using namespace std;

class Solution {
    public:
        int minimum_recolors(string blocks, int k) {
            int white_blocks = 0;
            int black_blocks = 0;
            int blocks_to_recolor = 0;

            for (int i = 0; i < k; i++) {
                if (blocks[i] == 'W') {
                    white_blocks++;
                } else {
                    black_blocks++;
                }
            }

            blocks_to_recolor = k-black_blocks;

            for (int i = k; i < blocks.size(); i++) {
                if (blocks[i] == 'W') {
                    white_blocks++;
                } else {
                    black_blocks++;
                }
                if (blocks[i-k] == 'W') {
                    white_blocks--;
                } else {
                    black_blocks--;
                }
                blocks_to_recolor = min(blocks_to_recolor,k-black_blocks);
            }

            return blocks_to_recolor;
        }
};

int main() {
    Solution test = Solution();

    string blocks1 = "WBBWWBBWBW";
    cout << test.minimum_recolors(blocks1, 7) << endl;

    string blocks2 = "WBWBBBW";
    cout << test.minimum_recolors(blocks2, 2) << endl;

    return 0;
}
