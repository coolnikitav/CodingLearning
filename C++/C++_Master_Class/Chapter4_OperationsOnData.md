# Precedence and associativity

- Multiplication and division first, addition and subtraction second
- Left to right
- [Operator Precedence Table](https://en.cppreference.com/w/cpp/language/operator_precedence)

# Prefix and Postfix Increment/Decrement
```C++
value = 5;
    
std::cout << "The value is (incrementing) : " << value++ << std::endl; // 5
std::cout << "The value is : " << value << std::endl; // 6

value = 5;
    
std::cout << "The value is (decrementing) : " << value-- << std::endl; //5
std::cout << "The value is : " << value << std::endl; // 4

value = 5;
std::cout << "The value is (prefix++ in place) : " << ++value << std::endl; // 6

value = 5;
std::cout << "The value is (prefix-- in place) : " << --value << std::endl;//4
```

# Output formatting
[Input/Output Manipulators](https://en.cppreference.com/w/cpp/io/manip)

# Weird Integral Types
Compiler only does arithmetic operations on data types of size 4 and up (int and up).

It cannot do operations on smaller types like char and short int. When you do mathematical operations with them, it converts them to int.
