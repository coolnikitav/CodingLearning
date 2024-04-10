## 3 - A.1
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/79e01d59-65c1-412b-9c83-fcbeca14995f)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6698e028-bcd0-4bbc-a915-4832f2dab383)

- load/store:
  - gap: 26.5 + 10.3 = 36.8%
  - gcc: 25.1 + 13.2 = 38.3%
  - average: (36.8+38.3)/2 = 37.55%
- alu instructions (add, sub, mul, compare, load imm, shift, AND, OR, XOR, other logical)
  - gap: 21.1 + 1.7 + 1.4 + 2.8 + 4.8 + 3.8 + 4.3 + 7.9 + 1.8 + 0.1 = 49.7%
  - gcc: 19.0 + 2.2 + 0.1 + 6.1 + 2.5 + 1.1 + 4.6 + 8.5 + 2.1 + 0.4 = 46.6%
  - average: 48.15%
- conditional branches:
  - gap: 9.3%
  - gcc: 12.1%
  - average: 10.7%
- jumps:
  - gap: 0.8%
  - gcc: 0.7%
  - average: 0.75%
 
CPI = 1.0 * 0.4815 + 1.4 * 0.3755 + 2.0 * 0.6 * 0.107 + 1.5 * 0.4 * 0.107 + 1.2 * 0.0075 = 0.4815 + 0.5257 + 0.1284 + 0.0642 + 0.009 = 1.2088

## 2 - 1.4
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/974d3f7c-608b-4ea9-ab45-03aaa225bf7d)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dd261a1e-45ab-4a76-8467-4602f1e459b4)

a.

Power needed = 66 + 2*2.3 + 7.9 = 78.5 W

Power supply is 80% efficient, so it should be 78.5/0.8 = 99 W

b.

power = 0.6*4 + 0.4*7.9 = 2.4 + 3.16 = 5.56

c.

seek7200 = 0.75 * seek5400

seek7200 + idle7200 = 100

seek5400 + idle5400 = 100

seek7200 * 7.9 + idle7200 * 4 = seek5400 * 7 + idle5400 * 2.9

idle5400 = 29.8%

## 1-H&P Ch 1.9
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/240a927a-acc1-4307-a87e-8188a0dffcc5)

Speedup = (old execution time)/(new execution time)

(old execution time) = 1

(new execution time) = 0.6 + 0.4/10 (it will spend 10 times less time on the 40% part)

speedup = 1/0.64 = 1.56
