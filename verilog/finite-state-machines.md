# Designing finite state machines

## Mealy vs Moore machine
Mealy machine depends on inputs and the present state.

Moore machine only depends on the present state.

## Mealy - 101 Non-overlapping sequence detector

When 101 is found, output will be 1. If its 10101, machine will not give the output twice.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f8a3bd76-1c65-4837-ad27-70bb3bbc470f)

## Mealy - 011 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c1538ac8-9570-4ac3-9fa6-3ea6b5f9fec7)

## Mealy - 000 non-overlapping sequence detector 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/83c255d7-8ea2-49ca-968f-ef1f7c6665f9)

## Mealy - 0101 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e3d3bd3e-0695-454d-95cd-794c4588f8dc)

## Mealy - 11011 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0a08ae42-2916-44d9-a0ff-13e4506bdc34)

## Mealy - 101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ceb3992d-a847-4f99-ae3d-4a3dc91f43ee)

## Mealy - 011 Overlapping sequence detector
Will behave the same way as non-overlapping because 011011, there are no bits that could overlap.
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/75280ae0-eacf-43e9-94a2-b456500015ac)

## Mealy - 000 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4e68db09-78f4-4fba-bf2f-31fafbeab3e3)

## Mealy - 0101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/05ba8c09-8b08-4035-9de6-e01004331d7d)

## Mealy - 11011 Overlapping Sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ea42afdf-dcb5-4848-902d-84179499e7e1)

## Designing a mealy machine - Sequence detector
We will write code for 001. It is the same for overlapping and non-overlapping.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dc93119f-7a3f-43f8-85df-5f33dc932210)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe2d0edd-18ef-482c-9a11-e1074475a243)

