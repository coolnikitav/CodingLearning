class Solution {
public:
    int maxOperations(vector<int>& nums, int k) {
        unordered_map<int, int> map;
        int pairCount = 0;

        for (int i = 0; i < nums.size(); i++) {
            int curr = nums[i];
            int dif = k - curr;
            if ((map.find(dif) != map.end()) && map[dif] != 0) { //if the number that completes the sum is available
                pairCount++;
                map[dif]--;                                      //use that number
            } else {
                map[curr]++;                                     //add a number to the map
            }
        }
        return pairCount;
    }
};
