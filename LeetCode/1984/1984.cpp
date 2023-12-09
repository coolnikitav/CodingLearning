#include<iostream>
#include<vector>
#include<algorithm>

using namespace std;

class Solution {
public:
    int minimumDifference(vector<int>& nums, int k) {
        sort(nums.begin(), nums.begin() + nums.size());

        int min_difference = INT_MAX;
        for (int i = 0; i < nums.size()-k+1; i++) {
            min_difference = min(min_difference, nums[i+k-1]-nums[i]);
        }

        return min_difference;
    }
};

int main() {
    Solution test = Solution();

    vector<int> nums1 = {90};
    cout << test.minimumDifference(nums1, 1) << endl;

    vector<int> nums2 = {9,4,1,7};
    cout << test.minimumDifference(nums2, 2) << endl;

    vector<int> nums3 = {1,3,2,5,8,4};
    cout << test.minimumDifference(nums3, 4) << endl;

    return 0;
}