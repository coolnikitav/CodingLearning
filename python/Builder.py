These 2 codes accomplish the same function:

class Solution {
public:
    bool isValidRows(vector<vector<char>>& board) {
        set<int> nums;
        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {
                if (board[i][j] != '.') {
                    if (nums.find(board[i][j]) != nums.end()) {
                        //cout << "isValidRows: false" << endl;
                        return false;
                    } else {
                        nums.insert(board[i][j]);
                    }
                }
            }
            nums.clear();
        }
        //cout << "isValidRows: true" << endl;
        return true;
    }

    bool isValidColumns(vector<vector<char>>& board) {
        set<int> nums;
        for (int j = 0; j < 9; j++) {
            for (int i = 0; i < 9; i++) {
                if (board[i][j] != '.') {
                    if (nums.find(board[i][j]) != nums.end()) {
                        //cout << "isValidColumns: false" << endl;
                        return false;
                    } else {
                        nums.insert(board[i][j]);
                    }
                }                
            }
            nums.clear();
        }
        //cout << "isValidColumns: true" << endl;
        return true;
    }

    bool isValidSquares(vector<vector<char>>& board) {
        set<int> nums;
        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
                for (int k = 0; k < 3; k++) {
                    for (int l = 0; l < 3; l++) {
                        //cout << "coordinates: " << 3*i+k << "," << 3*j+l << endl;
                        if (board[3*i+k][3*j+l] != '.') {
                            if (nums.find(board[3*i+k][3*j+l]) != nums.end()) {
                                //cout << "isValidSquares: false" << endl;
                                return false;
                            } else {
                                nums.insert(board[3*i+k][3*j+l]);
                            }
                        }
                    }
                }
                nums.clear();
            }
        }
        //cout << "isValidSquares: true" << endl;
        return true;
    }

    bool isValidSudoku(vector<vector<char>>& board) {
        return isValidRows(board) && isValidColumns(board) && isValidSquares(board);
    }
};

Code 2:
class Solution {
public:
    bool isValidSudoku(vector<vector<char>>& board) {
        unordered_map<int, set<int>> rows;
        unordered_map<int, set<int>> cols;
        unordered_map<int, set<int>> squares;

        int num;
        for (int r = 0; r < 9; r++) {
            for (int c = 0; c < 9; c++) {
                num = board[r][c];
                if (num != '.') {
                    // Check row
                    if (rows[r].find(num) != rows[r].end()) {
                        return false;
                    } else {
                        rows[r].insert(num);
                    }

                    // Check cols
                    if (cols[c].find(num) != cols[c].end()) {
                        return false;
                    } else {
                        cols[c].insert(num);
                    }

                    // Check square
                    if (squares[3*(r/3) + c/3].find(num) != squares[3*(r/3) + c/3].end()) {
                        return false;
                    } else {
                        squares[3*(r/3) + c/3].insert(num);
                    }
                }
            }
        }

        return true;
    }
};

Will one of them have a faster runtime?
