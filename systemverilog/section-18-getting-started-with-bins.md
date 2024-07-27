# Getting Started With Bins

## Fundamentals of Implicit/automatic bins
![image](https://github.com/user-attachments/assets/32711f32-940e-4f2c-a830-3393a9b34234)

![image](https://github.com/user-attachments/assets/5c76979e-6081-4a1e-895f-e745193b6c52)

![image](https://github.com/user-attachments/assets/a0b43965-2976-4da4-b26d-842d9386228e)

## Explicit bins
- Q: How to specify the bins to a single number? What about a range?
  
Implicit bins are created by the simulator and it tries to divide them evenly.

```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins zero = {0};
    bins one = {1};
    bins two = {2};
    bins three = {3};
  }
endgroup
```
