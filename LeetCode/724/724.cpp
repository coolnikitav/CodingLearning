class Solution {
public:
    int pivotIndex(vector<int>& nums) {
        int totalSum = 0;
        int leftSum = 0;

        for (int num : nums) {
            totalSum += num;
        }

        for (int i = 0; i < nums.size(); i++) {
            totalSum -= nums[i];
            if (leftSum == totalSum) {
                return i;
            } else {
                leftSum += nums[i];
            }
        }
        return -1;
    }
};
