class Solution {
public:
    int maximumDifference(vector<int>& nums) {
        int ans = -1;
        int min_num = nums[0];
        for (int i = 1; i < nums.size(); i++) {
            // Handle cases where nums[i] = nums[j]
            if (nums[i] > min_num) {
                ans = max(nums[i]-min_num, ans);
            } else {
                min_num = nums[i];
            }
        }

        return ans;
    }
};
