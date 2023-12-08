#include<iostream>
#include<vector>
#include<unordered_map>

using namespace std;

class Solution {
    public:
        int count_k_difference(vector<int>& nums, int k) {
            unordered_map<int, int> freq;

            for (int i = 0; i < nums.size(); i++) {
                freq[nums[i]]++;
            }

            int pairs = 0;

            for (auto item : freq) {
                if(freq.find(item.first+k) != freq.end()) {
                    pairs += item.second * freq[item.first+k];
                }

                if(freq.find(item.first-k) != freq.end()) {
                    pairs += item.second * freq[item.first-k];
                }
            }

            pairs /= 2;
            return pairs;
        }
};

int main() {
    Solution test = Solution();

    vector<int> nums1 = {1,2,2,1};
    cout << test.count_k_difference(nums1, 1) << endl;

    vector<int> nums2 = {1,3};
    cout << test.count_k_difference(nums2,3) << endl;

    vector<int> nums3 = {3,2,1,5,4};
    cout << test.count_k_difference(nums3,2) << endl;

    vector<int> nums4 = {1,1,5,5,-3};
    cout << test.count_k_difference(nums4,4) << endl;

    vector<int> nums5 = {3};
    cout << test.count_k_difference(nums5,2) << endl;

    return 0;
}
