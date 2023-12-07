#include<iostream>
#include<vector>

using namespace std;

class Solution {
    public:
        vector<int> replaceElements(vector<int>& arr) {
            int max = arr[arr.size()-1];
            int right_max = max;

            for (int i = arr.size()-2; i >= 0; i--) {
                if (arr[i] > max) {
                    max = arr[i];
                }

                arr[i] = right_max;
                right_max = max;
            }

            arr[arr.size()-1] = -1;

            return arr;
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

    vector<int> arr1 = {17,18,5,4,6,1};
    test.print_vector(test.replaceElements(arr1));

    vector<int> arr2 = {400};
    test.print_vector(test.replaceElements(arr2));

    return 0;
}
