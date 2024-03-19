# Branch Prediction

## Branch Cost Motivation
### Longer Frontends Means More Control Flow Penalty
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ad23523d-455d-4ca7-9ebf-3a1671208e11)

If you don't figure out if a branch is taken before execute stage, there will be more instructions to kill.

### Longer Pipeline Frontends Amplify Branch Cost
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a992a872-d60e-47e6-899a-d484bbcd9d93)

### Dual Issue and Branch Cost
If you go wide, it hurts more

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0b45c683-eb14-4c7f-b1f7-8282af414e45)

### Superscalars Multiply Branch Cost
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8e695087-f06e-4ad7-897e-a0b419e913c6)

## Branch Prediction Introduction

### Branch Prediction
Essential in modern processors to mitigate branch delay latencies

Two types of prediction:
1. Predict Branch Outcome
2. Predict Branch/Jump Address

### Where is the Branch Information Known?
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ace52f2d-e123-4b56-9ffb-8c6d58dd5d80)

JAL - jump and link, JR - jump register

## Static Outcome Prediction

### Branch Delay Slots (expose control hazard to software)

Change the ISA semantics so that the instructino that follows a jump or branch is always executed
- Gives compiler the flexibility to put in a useful instruction where normally a pipeline bubble would have resulted.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f44a8557-0d28-4374-bf17-95b83393a67a)

But usually its hard to find instructions to fill the slots

### Static Branch Prediction
Overall probability a branch is taken is ~60-70% but:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ca1d4f33-f81d-4f15-b7be-08c17e9a3834)

### Static Software Branch Prediction
Extend ISA to enable compiler to tell microarchitecture if branch is likely to be taken or not (Can be up to 80% accurate).

### Static Hardware Branch Prediction
1. Always Predict Not-Taken
   - What we have been assuming
   - Simple to implement
   - Know fall-through PC in Fetch
   - Poor accuracy, especially on backward branches
2. Always Predict Taken
   - Difficult to implement because don't know target until decode
   - Poor accuracy on if-then-else
3. Backward Branch Taken, Forward Branch Not Taken
   - Better accuracy
   - Difficult to implement becuase don't know target until decode
  
## Dynamic Outcome Prediction
### Dynamic Hardware Branch Prediction: Exploiting Temporal Correlation
Exploit structure in program: The way a branch resolves may be a good indicator of the way it will resolve the next time it executes (temporal correlation)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/93b1f070-b84b-4167-bf40-3aae685c5d75)

### 1-bit Saturating Counter
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cb7187a7-3281-43be-9a47-39118c1e7cad)

### 2-bit Saturating Counter
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1b7a4511-601a-4ac0-b5f3-c9cef0e3af64)

### Other 2-bit FSM Branch Predictors
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d7a0e2d2-b8de-46bd-8ef2-fe279ba6f3ab)

### Branch History Table (BHT)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/be0d5ebd-5fef-4578-98cf-e0aaca7c7c29)

### Exploiting Spatial Correlation
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1a368d1b-40a3-4444-8b12-c7f5d5de7467)

If first condition false, second condition also false.

Brach History Register, BHR, records the direction of the last N branches executed by the processor (shift register)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a622b1ad-7f80-4a94-8c0d-20ddf1f53f92)

### Pattern History Table (PHT)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4a817598-f7bf-4551-9c20-752bf229d0b3)

### Two-Level Branch Predictor
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/99a13961-1e52-4a1b-a2b6-12bce7d17bf1)

### Generalize Two-Level Branch Predictor
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b0400e65-5e1e-4816-8fbb-cead46e50922)

### Tournament Predictors
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/24cbf4db-0b35-421c-89f7-6e988a739d25)

- Choice predictor learns whether best to use local or global branch history in predicting next branch.
- Global history is speculatively updated but restored on mispredict
- Claim 90-100% success on range of applications

## Target Address Prediction
### Predicting Target Address
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3a160da9-c0fd-4a52-b4e1-106e2c0a08be)

Even with best possible prediction of branch outcome, still have to wait for branch target address to be determined.

### Branch Target Buffer (BTB)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0182cfbd-52f7-4973-9a8f-1ad1225c3a81)

### BTB is only for Control Instructions
- BTB contains useful information for branch and jump instructions only
  - Do not update it for other instructions
- For all other instructions the next PC is PC+4!

How to achieve this effect without decoding the instruction?

When do we update BTB information?

### Uses of Jump Register (JR)
- Switch statements (jump to address of matching case)
  - BTB works well if same case used repeatedly
- Dynamic function call (jump to run-time function address)
  - BTB works well if same function usually called, (e.g., in C++ programming, when objects have same type in virtual function call)
- Subroutine returns (jump to return address)
  - BTB works well if usually return to the same place => Often one function called from many distinct call sites!

### Subroutine Return Stack
Small structure to accelerate JR for subroutine returns, typically much more accurate than BTBs.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8a59ed94-858e-400a-b051-eec83fe94f18)
