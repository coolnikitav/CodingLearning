# Digital Logic Design

## Number Systems, Arithmetic, and Codes

### 1. Convert following decimal numbers in signed binary, octal and hex nums using minimum possible number of bits
- (17)d = 0b01_0001 = 0x11 = 0o21
- (-17)d = 0b10_1111 = 0xEF = 0o57

### 2. What is the decimal equivalent of 0x3A?
- 0x3A = (3*16 + 10)d = 58d

### 3. What is Gray code and what are some of the benefits of using Gray code over Binary code?
- Gray code is a binary system in which consecutive numbers only differ by 1 bit. The benefit is that there are less errors since only 1 bit is changing (multiple bits can take different time to transition). G3 = B3, G2 = B3^B2, G1=B2^B1, G0=B1^B0

### 4. What is a parity bit and how is it computed?
- A parity bit is used as a simple way of detecting errors. If even parity then the total count of 1 (including parity bit) should be even. For odd its odd. Parity bit is computed by taking XOR of all the bits.

### 5. For a given binary string: 111001, compute the proper odd parity bit.
- Odd parity bit should be 1. That would make the number have odd number of bits.

### 6. What are 1's complement and 2's complement? Where are they used?
- They are ways of representing negative numbers in signed number systems.
- 1's complement is achieved by flipping all the bits in a binary number.
- 2's complement is 1's complement + 1
- 2's complement is used everywhere in computing to represent negative numbers

### 7. What is a BCD code and how is it different from binary code? What will be the BCD and binary code for decimal number 27?
- BCD is binary coded decimal. It is a form of binary conversion where each digit is represented independently.
- (27)d = 0b0010_0111

### 8. Which of the following code can represent numbers, characters, and special characters? BCD, Gray, EBCDIC code, ASCII code, Alphanumeric code?
- Alpanumeric code

### 9
