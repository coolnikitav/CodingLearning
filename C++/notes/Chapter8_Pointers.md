All pointer variables have the same size.

Position of the * doesn't matter.

Pointer only stores the type for which it was declared:
```C++
int *p_int1 {nullptr};
double double_var {33};

p_int1 = &double_var;  //compiler error
```

If you initialize the array with a pointer, you cannot modify it:
```C++
char* p_message {"Hello World"};
```
