int countSegments(char* s) {
    int segments_count = 0;
    bool prev_inside_segment = false;
    bool inside_segment = false;

    for (int i = 0; i < strlen(s); i++) {
        inside_segment = s[i] == ' ' ? false : true;
        if (inside_segment && !prev_inside_segment) {
            segments_count++;
        }
        prev_inside_segment = inside_segment;
    }

    return segments_count;
}
