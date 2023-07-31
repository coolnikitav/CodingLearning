class Solution {
public:
    double findMaxAverage(vector<int>& nums, int k) {
        double avg = 0;
        for (int i = 0; i < k; i++) {
            avg += (double)nums[i]/k;
        }

        double temp = avg;
        for (int i = 0, j = k; j < nums.size(); i++, j++) {
            temp += (double)(nums[j] - nums[i])/k;  //include next num and remove first num from temp avg
            if (temp > avg) {
                avg = temp;
            }
        }
        return avg;
    }
};
