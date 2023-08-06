#include <vector>
#include <unordered_map>

class Solution {
public:
    vector<vector<int>> findDifference(vector<int>& nums1, vector<int>& nums2) {
        vector<int> output1;
        vector<int> output2;

        unordered_map<int, int> map1;
        unordered_map<int, int> map2;

        for (auto i : nums1) {
            map1[i] = 1;
        }

        for (auto i : nums2) {
            map2[i] = 1;
        }

        for (auto i : nums1) {
            if (map2.find(i) == map2.end() && map1[i] == 1) {   // If num is not in the other map and
                                                                // hasn't been added to the list
                output1.push_back(i);
                map1[i]--;
            }
        }

        for (auto i : nums2) {
            if (map1.find(i) == map1.end() && map2[i] == 1) {   // If num is not in the other list and
                                                                // hasn't been added to the list
                output2.push_back(i);
                map2[i]--;
            }
        }

        vector<vector<int>> answer;
        answer.push_back(output1);
        answer.push_back(output2);
        return answer;
    }
};
