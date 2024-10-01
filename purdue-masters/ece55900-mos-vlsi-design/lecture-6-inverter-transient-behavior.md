# Inverter: Transient Behavior

## MOSFETS: Transient Response
![image](https://github.com/user-attachments/assets/7bab1bd1-29e8-48cf-82c2-d0c4d1a150c0)

## Obtaining Transient Response To A Step Input
- Q: What is the equation for V_OUT when V_IN goes from 0 to V_DD? What about when V_IN goes from V_DD to 0?
  
![image](https://github.com/user-attachments/assets/7a84f106-9a14-48cf-ab9a-1063565512a4)

Note: it is assumed that the input is a step input.

## Obtaining Propagation Delay
- Q: Express the T_PHL and T-PLH in terms of resistances and capacitances.
  
![image](https://github.com/user-attachments/assets/df9af155-7a5d-4060-b01f-b9a527a49e84)

## Obtaining Rise/Fall Time
![image](https://github.com/user-attachments/assets/39d239c8-d6c5-4c98-aec4-255a4fa9ae45)

## Obtaining Transient Response: A More Rigorous Approach
- Q: What is the equation for I_N in terms of Vout and C_L:
  ![image](https://github.com/user-attachments/assets/0fb3dd16-259f-4699-83c0-0a1355567e1d)

![image](https://github.com/user-attachments/assets/83769c9d-9297-4a8f-8d16-020e87baa97a)

I_N(V_OUT) means I_N is a function of V_OUT

![image](https://github.com/user-attachments/assets/5f4c0d6a-4ded-4530-bc73-fdcb3b884955)

![image](https://github.com/user-attachments/assets/c791c1a3-43ac-4183-b986-beffe81a45e0)

![image](https://github.com/user-attachments/assets/72461ada-0078-426d-8d74-c51cdfe8d212)

![image](https://github.com/user-attachments/assets/c4186bf5-28e4-4f2e-b219-8e1e39b60b7b)

## Summary V_DD/2 > V_TSBN
![image](https://github.com/user-attachments/assets/60bc3894-3cf2-40d6-a64e-e530cb9cd3ad)

## Summary V_DD/2 < V_TSBN
![image](https://github.com/user-attachments/assets/07e217d3-b9d5-43dc-842d-5687b2d887b6)

## Rise Time and Fall Time
![image](https://github.com/user-attachments/assets/57035930-bc57-40c6-af5c-7771aedfb2d3)

The function is complicated

## Load Capacitance
- Q: Let's say we have inverter 1 connected to inverter 2. Draw all of the load capacitances that are affecting inverter1.

![image](https://github.com/user-attachments/assets/360f8a14-daac-4c42-a424-11d77c226f44)

## Miller Capacitance
![image](https://github.com/user-attachments/assets/47e26e2f-a8b8-4aa5-b15b-1113741cdfca)

## Fanout (FO)
![image](https://github.com/user-attachments/assets/47ffaba8-1fda-4b26-ae1f-b9ec854b8137)

Fanout is determined in terms of C_L_EXT only, not C_L_INT.

## Increase In Delay Due To Finite Input Slew Rate
![image](https://github.com/user-attachments/assets/6d5f4ba9-cdc4-47e7-ab08-e4832b943f4a)

## Decrease In Delay With Increasing V_DD
- Q1: What is the cost you are paying with increasing V_DD?
- Q: Why does delay decrease with increase in V_DD?

![image](https://github.com/user-attachments/assets/d07ad95f-8329-42ef-937c-e858103223a7)

- A1: More power/energy use.

## Impact Of Transistor Sizing
- Q: When s increases, does intrinsic capacitance increase/decrease? What about resistance of the MOSFETs?
- Q: Draw delay vs s graph. Explain why its steep in some places and flat in others.

![image](https://github.com/user-attachments/assets/8139c2a1-d01e-47d6-ae96-bd0828e253c3)

## Impact Of W_P/W_N
![image](https://github.com/user-attachments/assets/fca622ac-b2f5-49e1-a799-179d6f9ed9c4)

## Optimal W_P/W_N For Minimum Avg. Delay
![image](https://github.com/user-attachments/assets/5bf31f16-a0c0-4ac2-bab9-03faa4bce817)

- Q: What are C_IN, C_LINT, and C_L in terms of gate, drain, and load capacitances?

![image](https://github.com/user-attachments/assets/fa719a7d-2255-4fd5-ac46-23938a9d5e49)

![image](https://github.com/user-attachments/assets/6a1bae3a-2159-45c2-ba0a-99370f8007c2)

![image](https://github.com/user-attachments/assets/fbe7c137-41f5-4554-8f4c-9cab8255d895)

## Simple Expression For Inverter Delay For A Fixed beta
- Q: What is the expression for both propagation delays in terms of R_N, R_P, and C_L?
  
![image](https://github.com/user-attachments/assets/9923133a-ff6d-416f-afe5-e8c2ebbf1595)

![image](https://github.com/user-attachments/assets/df9d72f5-06a6-40e8-a6eb-eb6c491d0607)

![image](https://github.com/user-attachments/assets/8178dc6f-4502-4643-acce-b12757ca7e96)

- Q: What is the propagation delay in terms of the intrinsic delay and fanout?

![image](https://github.com/user-attachments/assets/d9bbbc33-68bd-43db-ac87-8d3809db4f1a)

![image](https://github.com/user-attachments/assets/53ebb1ae-1705-4ecd-b557-4f3d32f829d1)

![image](https://github.com/user-attachments/assets/a75c2229-9546-4b3b-87cf-6af98c358aa3)

## Example
![image](https://github.com/user-attachments/assets/24061483-6dd2-4782-8586-3fa0ed130cf8)
