#include<iostream>
#include<vector>
#include<map>

using namespace std;

class Solution {
    public:
        int find_speciall_integer(vector<int>& arr) {
            int qtr = arr.size()/4;
            int count = 1;
            int curr = arr[0];

            for (int i = 1; i < arr.size(); i++) {
                if (curr == arr[i]) {
                    count++;
                    if (count > qtr) {
                        return curr;
                    }
                } else {
                    count = 1;
                    curr = arr[i];
                }
            }
            return curr; 
        }
};

int main() {
    Solution test = Solution();

    vector<int> arr1 = {1,2,2,6,6,6,6,7,10};
    cout << test.find_speciall_integer(arr1) << endl;

    vector<int> arr2 = {1,1};
    cout << test.find_speciall_integer(arr2) << endl;

    vector<int> arr3 = {1,2,3,3};
    cout << test.find_speciall_integer(arr3) << endl;

    return 0;
}
