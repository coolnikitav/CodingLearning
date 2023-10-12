#include <iostream>

consteval int get_value() {
    return 3;
}

int main() {
    std::cout << "Number 1" << std::endl;
    std::cout << "Number 2" << std::endl;
    
    return 0;
}