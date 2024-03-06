void findRook(char** board, int boardSize, int boardColSize, int* rook_x, int* rook_y) {
    int x,y;

    for (int i = 0; i < boardSize; i++) {
        x = i/(boardColSize);
        y = i%(boardColSize);
        if (board[x][y] == 'R') {
            *rook_x = x;
            *rook_y = y;
            break;
        }
    }
}

int countUp(char** board, int x, int y) {
    for (int i = y-1; i >= 0; i--) {
        if (board[x][i] == 'p') {
            return 1;
        } else if (board[x][i] == 'B') {
            return 0;
        }
    }
    return 0;
}

int countRight(char** board, int boardColSize, int x, int y) {
    for (int i = x+1; i < boardColSize; i++) {
        if (board[i][y] == 'p') {
            return 1;
        } else if (board[i][y] == 'B') {
            return 0;
        }
    }
    return 0;
}

int countDown(char** board, int boardColSize, int x, int y) {
    for (int i = y+1; i < boardColSize; i++) {
        if (board[x][i] == 'p') {
            return 1;
        } else if (board[x][i] == 'B') {
            return 0;
        }
    }
    return 0;
}

int countLeft(char** board, int x, int y) {
    for (int i = x-1; i >= 0; i--) {
        if (board[i][y] == 'p') {
            return 1;
        } else if (board[i][y] == 'B') {
            return 0;
        }
    }
    return 0;
}

int count_captures(char** board, int boardColSize, int x, int y) {
    return countUp(board, x, y) + countRight(board, boardColSize, x, y) + countDown(board, boardColSize, x, y) + countLeft(board, x, y);
}

int numRookCaptures(char** board, int boardSize, int* boardColSize) {
    int rook_x = -1;
    int rook_y = -1;

    findRook(board, boardSize, *boardColSize, &rook_x, &rook_y);

    int available_captures = 0;

    return count_captures(board, *boardColSize, rook_x, rook_y);
}

int main() {
    int boardColSize = 8;
    char board1[8][8] = {{'.','.','.','.','.','.','.','.',},
                         {'.','.','.','p','.','.','.','.'},
                         {'.','.','.','R','.','.','.','p'},
                         {'.','.','.','.','.','.','.','.'},
                         {'.','.','.','.','.','.','.','.'},
                         {'.','.','.','p','.','.','.','.'},
                         {'.','.','.','.','.','.','.','.'},
                         {'.','.','.','.','.','.','.','.'}};
    char* boardPtrs1[8];
    for (int i = 0; i < 8; i++) {
        boardPtrs1[i] = board1[i];
    }
    printf("%d\n",numRookCaptures(boardPtrs1, 64, &boardColSize));                    

    char board2[8][8] = {{'.','.','.','.','.','.','.','.'},
                         {'.','p','p','p','p','p','.','.'},
                         {'.','p','p','B','p','p','.','.'},
                         {'.','p','B','R','B','p','.','.'},
                         {'.','p','p','B','p','p','.','.'},
                         {'.','p','p','p','p','p','.','.'},
                         {'.','.','.','.','.','.','.','.'},
                         {'.','.','.','.','.','.','.','.'}};
    char* boardPtrs2[8];
    for (int i = 0; i < 8; i++) {
        boardPtrs2[i] = board2[i];
    }
    printf("%d\n",numRookCaptures(boardPtrs2, 64, &boardColSize));

    char board3[8][8] = {{'.','.','.','.','.','.','.','.'},
                         {'.','.','.','p','.','.','.','.'},
                         {'.','.','.','p','.','.','.','.'},
                         {'p','p','.','R','.','p','B','.'},
                         {'.','.','.','.','.','.','.','.'},
                         {'.','.','.','B','.','.','.','.'},
                         {'.','.','.','p','.','.','.','.'},
                         {'.','.','.','.','.','.','.','.'}};
    char* boardPtrs3[8];
    for (int i = 0; i < 8; i++) {
        boardPtrs3[i] = board3[i];
    }
    printf("%d\n",numRookCaptures(boardPtrs3, 64, &boardColSize));

    return -1;
}
