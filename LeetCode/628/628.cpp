#include<iostream>
#include<vector>

using namespace std;

class Solution {
public:
    int maximumProduct(vector<int>& nums) {
        int first_max = -1001;
        int first_min = 1001;
        int second_max, third_max, second_min;

        for (int i = 0; i < nums.size(); i++) {
            if (nums[i] >= first_max) {
                third_max = second_max;
                second_max = first_max;
                first_max = nums[i];
            } else if (nums[i] >= second_max) {
                third_max = second_max;
                second_max = nums[i];
            } else if (nums[i] >= third_max) {
                third_max = nums[i];
            } 
            if (nums[i] <= first_min) {
                second_min = first_min;
                first_min = nums[i];
            } else if (nums[i] <= second_min) {
                second_min = nums[i];
            }
        }
        // cout << "first_max: " << first_max << " second_max: " << second_max << " third_max: " << third_max << " first_min: " << first_min << " second_min: " << second_min << endl;
        if (first_min != 1001 && second_min != 1001) {
            return max(first_max * second_max * third_max, first_max * first_min * second_min);
        }
        return first_max * second_max * third_max;
    }
};

int main() {
    Solution test = Solution();

    vector<int> nums1 = {1,2,3};
    vector<int> nums2 = {1,2,3,4};
    vector<int> nums3 = {-1,-2,-3};
    vector<int> nums4 = {7,4,2,7,8,4,11};
    vector<int> nums5 = {-100, 3, 7, 8, -2};

    cout << test.maximumProduct(nums1) << endl;
    cout << test.maximumProduct(nums2) << endl;
    cout << test.maximumProduct(nums3) << endl;
    cout << test.maximumProduct(nums4) << endl;
    cout << test.maximumProduct(nums5) << endl;

    return 0;
}
