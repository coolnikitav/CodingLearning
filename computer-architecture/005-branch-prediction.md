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
