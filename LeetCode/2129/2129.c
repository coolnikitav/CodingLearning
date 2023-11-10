#include<stdio.h>
#include<ctype.h>
#include<string.h>
#include<stdlib.h>
#include<stdbool.h>

void modify_word(char* capitalized_string, char* title, int* from_index, int* to_index, bool more_than_two_chars) {
    if (more_than_two_chars) {
        capitalized_string[*from_index] = toupper(title[*from_index]);
        (*from_index)++;
    }
    
    while (*from_index < *to_index) {
        capitalized_string[*from_index] = tolower(title[*from_index]);
        (*from_index)++;
    }
}

char* capitalizeTitle(char* title) {
    int title_length = strlen(title);
    char* capitalized_string = (char*)malloc(title_length*sizeof(char));

    int index = 0;          int* index_ptr = &index;
    int forward_index = 0;  int* forward_index_prt = &forward_index;

    while (forward_index < title_length) {
        while (title[forward_index] != ' ' && title[forward_index] != '\0') {
            forward_index++;
        }
        if (forward_index < title_length) { 
            capitalized_string[forward_index] = ' '; 
        }

        if (forward_index - index > 2) {
            modify_word(capitalized_string, title, index_ptr, forward_index_prt, true);
        } else {
            modify_word(capitalized_string, title, index_ptr, forward_index_prt, false);
        }

        index++;
        forward_index++;
    }

    return capitalized_string;
}

int main() {
    char* title1 = "capiTalIze tHe titLe";
    printf(".%s.\n", capitalizeTitle(title1));

    char* title2 = "First leTTeR of EACH Word";
    printf(".%s.\n", capitalizeTitle(title2));

    char* title3 = "i lOve leetcode";
    printf(".%s.\n", capitalizeTitle(title3));
    return 0;
}
