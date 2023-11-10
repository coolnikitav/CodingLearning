#include<stdio.h>

int calculate_player_score(int* player, int playerSize) {
    int total_score = 0;
    int turns_since_last_strike = 2;

    for (int i = 0; i < playerSize; i++) {
        if (turns_since_last_strike < 2) {
            total_score += 2*player[i];
        } else {
            total_score += player[i];
        }
        if (player[i] == 10) {
            turns_since_last_strike = 0;
        } else {
            turns_since_last_strike++;
        }
    }

    return total_score;
}

int isWinner(int* player1, int player1Size, int* player2, int player2Size) {

    int player1_score = calculate_player_score(player1, player1Size);
    int player2_score = calculate_player_score(player2, player2Size);
    printf("Player 1 score: %d, ", player1_score);
    printf("Player 2 score: %d\n", player2_score);

    if (player1_score == player2_score) {
        return 0;
    } else {
        return player1_score > player2_score ? 1 : 2;
    }
}

int main() {
    int player1_1[4] = {4,10,7,9};
    int player2_1[4] = {6,5,2,3};
    printf("%d\n", isWinner(player1_1, 4, player2_1, 4));

    int player1_2[4] = {3,5,7,6};
    int player2_2[4] = {8,10,10,2};
    printf("%d\n", isWinner(player1_2, 4, player2_2, 4));

    int player1_3[2] = {2,3};
    int player2_3[2] = {4,1};
    printf("%d\n", isWinner(player1_3, 2, player2_3, 2));

    return 0;
}
