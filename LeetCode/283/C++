class Solution {
public:
    void moveZeroes(vector<int>& nums) {
        for (int i = 1, temp = 0; i < nums.size(); i++) {
            if (nums[temp] == 0 && nums[i] != 0) {          //swap elements if [0,x]
                nums[temp] = nums[i];
                nums[i] = 0;
                temp++;
            } else if (nums[i] != 0 || nums[temp] != 0) {   //temp should stay at last non-zero num
                temp++;
            }
        }
    }
};
