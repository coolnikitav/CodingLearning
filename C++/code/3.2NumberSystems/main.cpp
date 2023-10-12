#include <iostream>

int main() {

    int num1 = 15;          //Decimal
    int num2 = 017;         //Octal
    int num3 = 0x0f;        //Hexadecimal
    int num4 = 0b00001111;  //Binary

    std::cout << "num1 : " << num1 << std::endl;
    std::cout << "num2 : " << num2 << std::endl;
    std::cout << "num3 : " << num3 << std::endl;
    std::cout << "num4 : " << num4 << std::endl;
    return 0;
}