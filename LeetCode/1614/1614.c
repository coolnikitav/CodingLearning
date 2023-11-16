int maxDepth(char* s) {
    int max_depth = 0;
    int curr_depth = 0;

    for (int i = 0; i < strlen(s); i++) {
        if (s[i] == '(') {
            curr_depth++;
            if (curr_depth > max_depth) {
                max_depth = curr_depth;
            }
        } else if (s[i] == ')') {
            curr_depth--;
        }
    }

    return max_depth;
}
