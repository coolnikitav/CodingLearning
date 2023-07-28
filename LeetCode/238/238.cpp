class Solution {
public:
    vector<int> productExceptSelf(vector<int>& nums) {
        int length = nums.size();

        vector<int> output(length, 1);

        int pre = 1;
        int suf = 1;

        for (int i = 0; i < length; i++) {
            output[i] *= pre;
            pre *= nums[i];
            output[length-1-i] *= suf;
            suf *= nums[length-1-i];
        }

        return output;
    }
};
