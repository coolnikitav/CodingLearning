class Solution {
public:
    int largestAltitude(vector<int>& gain) {
        int altitude {0};
        int temp {0};
        for (int altitudeGain : gain) {
            temp += altitudeGain;
            altitude = max(altitude, temp);
        }
        return altitude;
    }
};
