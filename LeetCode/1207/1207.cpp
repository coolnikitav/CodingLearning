#include <unordered_map>

class Solution {
public:
    bool uniqueOccurrences(vector<int>& arr) {
        unordered_map<int, int> map;
        unordered_map<int, int> temp;

        for (auto i : arr) {
            map[i]++;
        }

        for (auto i : map) {
            if (temp.find(i.second) != temp.end()) {
                return false;
            } else {
                temp[i.second] = 1;
            }
        }

        return true;
    }
};
