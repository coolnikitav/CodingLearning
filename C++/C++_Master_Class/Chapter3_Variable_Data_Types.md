## Integers
```C++
int count;      //variable may contain random garbage value
int count {5};  //braced initialization
int count(5);  //functional initialization
int count = 5;  //assignment initialization
```

integers are signed by default. 

Signed range: [-2^(n-1) -> 2^(n-1) - 1]

Unsigned range: [0 -> 2^n - 1]

These only work with integers:
- short = 2 bytes
- int = 4 bytes
- long = 4 or 8 bytes
- long long = 8 bytes

## Fractional numbers:
- float = 4 bytes, 7 precision
- double = 8 bytes, 15 precision
- long double = 12 bytes, > double

When the precision ends, compiler prints random digits.

Double is default, so add suffix to float and long double:
- float num1 {1.124324523f};           (without the "f", compiler would think its a double being casted to a float)
- double num1 {1.2343223423};
- long double num1 {1.234324236464L};

## Boolean
```C++
bool word {true};  //sizeof(bool) = 1
```

## Characters
```C++
char value {'A'};
char value = 65;  //ASCII character code for 'A'
std::cout << "value : " << value << std::endl;
std::cout << "value(int) : << static_cast<int>(value) << std::endl;
```

## Auto
Compiler decides the variable type on its own.

Be careful with assigning auto variables to a different type than was at declaration.
