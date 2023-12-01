#include<stdio.h>
#include<string.h>
#include<stdlib.h>

int minLength(char * s){
    int length = strlen(s);
    char* stack =(char *)malloc(sizeof(char) * (length+1));
    int top = 0;

    for (int i = 0; i < length; i++) {
        if ((stack[top] == 'A' && s[i] == 'B') || (stack[top] == 'C' && s[i] == 'D')) {
            top--;
        } else {
            stack[++top] = s[i];
        }
    }
    
    free(stack);
    return top;
}


int main() {
    char s1[9] = "ABFCACDB";
    printf("%d\n", minLength(s1));

    char s2[6] = "ACBBD";
    printf("%d\n", minLength(s2));

    char s3[11] = "CCDAABBDCD";
    printf("%d\n", minLength(s3));

    return 0;
}
