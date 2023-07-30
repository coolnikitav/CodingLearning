# Compiler

## Windows

- Download GCC and Clang [here](https://winlibs.com/).

- Extract to C drive.

- Copy "C:\mingw64\bin", go to environment variables -> system variables -> path -> edit -> add the new variable.

- To test whether compilers are working: go to command prompt, "g++ --version", "clang++ --version".

- Open VSCode. Install C/C++ extension.

- Open a .cpp file. Terminal -> configure tasks -> choose g++ compiler.

- Go to tasks.json. Add "-std=c++20" flag to "args".

- Terminal -> run task -> select the build.

- .exe file is created. Navigate to the folder and run ./filename.exe.

- Open command pallete. Go to C/C++: edit configurations. Set C++ standard to c++20.

## Linux
