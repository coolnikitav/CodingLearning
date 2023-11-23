#include<stdio.h>
#include<math.h>

int findComplement(int num) {
    int num_of_bits = 1;
    while (pow(2,num_of_bits)-1 < num) {
        num_of_bits++;
    }
    int bit_mask = pow(2,num_of_bits)-1;  

    return num ^ bit_mask;
}

int main() {
    printf("%d\n", findComplement(5));

    printf("%d\n", findComplement(1));
    return 0;
}
