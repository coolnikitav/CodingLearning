bool compare_words(char* word1, char* word2, int* int_order) {
    int i = 0;
    while (word1[i] != '\0') {
        if (word2[i] == '\0') {
            return false;
        }

        if (int_order[word1[i]-97] < int_order[word2[i]-97]) {
            return true;
        }
        else if (int_order[word1[i]-97] > int_order[word2[i]-97]) {
            return false;
        }
        i++;
    }
    return true;
}

bool isAlienSorted(char ** words, int wordsSize, char * order){
    if (wordsSize == 1) {
        return true;
    }
    // Create a map from order array based on ASCII values
    int int_order[26];

    for (int i = 0; i < 26; i++) {
        int_order[order[i]-97] = i;
    }

    for (int i = 0; i < wordsSize-1; i++) {
        if (!compare_words(words[i], words[i+1], int_order)) {
            return false;
        }
    }
    return true;
}
