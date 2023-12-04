class Solution {
public:
    bool squareIsWhite(string coordinates) {
        if (coordinates[0] % 2 == 1) {  //a,c,e,g
            if (coordinates[1] % 2 == 1) {  // 1,3,5,7
                return false;
            } else {
                return true;
            }
        } else {    // b,d,f,h
            if (coordinates[1] % 2 == 1) {
                return true;
            } else {
                return false;
            }
        }
    }
};
