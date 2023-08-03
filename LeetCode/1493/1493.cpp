class Solution {
public:
    int longestSubarray(vector<int>& nums) {
        int zeroes = 0;
        int start = 0;
        int longest = 0;

        for (int i = 0; i < nums.size(); i++) {
            if (nums[i] == 0) {
                zeroes++;
            }
            // Shrink the window until the zero counts come under the limit.
            while (zeroes > 1) {
                if (nums[start] == 0) {
                    zeroes--;
                }
                start++;
            }
            longest = max(longest, i - start);
        }

        return longest;
    }
};
