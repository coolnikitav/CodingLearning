#include<iostream>
#include<vector>
#include<unordered_map>

using namespace std;

class Solution {
    public:
        vector<int> number_of_pairs(vector<int>& nums) {
            unordered_map<int,int> freq;

            for (int i = 0; i < nums.size(); i++) {
                freq[nums[i]]++;
            }

            int pairs = 0;
            int leftover = 0;

            for (auto i : freq) {
                if (i.second % 2 == 1) {
                    leftover++;
                }

                pairs += i.second / 2;
            }

            return {pairs, leftover};
        }

        void print_vector(vector<int> nums) {
            cout << "{";
            for (int i = 0; i < nums.size()-1; i++) {
                cout << nums[i] << ", ";
            }
            cout << nums[nums.size()-1] << "}" << endl;
        }
};

int main() {
    Solution test = Solution();

    vector<int> nums1 = {1,3,2,1,3,2,2};
    test.print_vector(test.number_of_pairs(nums1));
    
    vector<int> nums2 = {1,1};
    test.print_vector(test.number_of_pairs(nums2));

    vector<int> nums3 = {0};
    test.print_vector(test.number_of_pairs(nums3));

    return 0;
}
