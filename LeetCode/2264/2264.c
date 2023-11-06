char* largestGoodInteger(char* num) {
    char max = '-';

    int length = strlen(num);

    for (int i = 0; i < length-2; i++) {
        if (num[i] == num[i+1]) {
            if (num[i+1] == num[i+2]) {
                if (num[i] > max) {
                    max = num[i];
                }
            }
        }
    }

    if (max == '-') {
        return "";
    }

    char* good = (char*)malloc(4*sizeof(char));
    good[0] = max;
    good[1] = max;
    good[2] = max;
    good[3] = '\0';
    
    return good;
}
