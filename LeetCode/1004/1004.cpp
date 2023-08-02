lass Solution {
public:
    int longestOnes(vector<int>& nums, int k) {
        int onesCount = 0;
        int temp = 0;

        int beg = 0;
        int end = 0;

        //find number of ones we can get by flipping the first k zeroes
        while (end < nums.size() && (k > 0 || nums[end] == 1)) { 
            temp++;
            if (nums[end] == 0) {
                k--;
            }
            end++;
        }
        onesCount = temp;

        while (end < nums.size()) {
            if (nums[end] == 1) {
                temp++;
            } else if (nums[end] == 0) {
                //if a new zero is encountered, bring the beginning of the window up to the first k zero
                while (nums[beg] == 1) {
                    beg++;
                }
                temp = end - beg;
                beg++;
            }
            onesCount = max(onesCount, temp);
            end++;
        }
        return onesCount;
    }
};
