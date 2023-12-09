#include<iostream>
#include<vector>

using namespace std;

class Solution {
    public:
        int maximum_count(vector<int>& nums) {
            int pos = 0;
            int neg = 0;

            for (int i = 0; i < nums.size(); i++) {
                if (nums[i] > 0) {
                    pos++;
                } else if (nums[i] < 0) {
                    neg++;
                }
            }

            return max(pos,neg);
        }
};

int main() {
    Solution test = Solution();

    vector<int> nums1 = {-2,-1,-1,1,2,3};
    cout << test.maximum_count(nums1) << endl;

    vector<int> nums2 = {-3,-2,-1,0,0,1,2};
    cout << test.maximum_count(nums2) << endl;

    vector<int> nums3 = {5,20,66,1314};
    cout << test.maximum_count(nums3) << endl;

    return 0;
}