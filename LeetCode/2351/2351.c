int search_array(char * arr, int letter_count, char letter) {
    for (int i = 0; i < letter_count; i++) {
        if (arr[i] == letter) {
            return 1;
        }
    }
    return 0;
}

char repeatedCharacter(char * s){
    int s_len = strlen(s);
    char *traversed_array = (char *)malloc(s_len * sizeof(char));

    for (int i = 0; i < s_len; i++) {
        if (search_array(s, i, s[i]) == 1) {
            free(traversed_array);
            return s[i];
        }
        traversed_array[i] = s[i];
    }
    free(traversed_array);
    return ']';
}
