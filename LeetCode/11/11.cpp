#include <vector>

using namespace std;
class Solution {
public:
    int maxArea(vector<int>& height) {
        int area = 0;

        /*
         * Find area between beginning and end. Then move away from the 
         * smaller number and check the new area.
         */
        for (int front = 0, back = height.size()-1; front != back;) {
            int tempArea = min(height[front], height[back]) * (back - front);
            if (tempArea > area) {
                area = tempArea;
            }
            if (height[front] <= height[back]) {
                front++;
            } else {
                back--;
            }
        }
        return area;
    }
};
