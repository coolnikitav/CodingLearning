# Chapter 5

## Module 5.1 Overview of Superscalar Processors

### This Unit: Multiple Issue/Static Scheduling
![image](https://github.com/user-attachments/assets/8efc5924-5c81-4a7c-8571-4af7d0a15cc1)

### Scalar Pipeline and the Flynn Bottleneck
![image](https://github.com/user-attachments/assets/dd97e794-a5db-4a75-82df-0bcad5f6ee4e)

### Multi-Issue Pipeline
![image](https://github.com/user-attachments/assets/fd0556e6-d680-4291-93a6-8ecdbaa34e23)

### Superscalar Execution
![image](https://github.com/user-attachments/assets/c218dfc2-7e8a-4a14-88cc-f441294de9fa)

### Superscalar Challenges - Front End
![image](https://github.com/user-attachments/assets/21c3ef29-bffd-4cbe-9e89-e7cc9f79060c)

### Superscalar Challenges - Back End
![image](https://github.com/user-attachments/assets/5256e90e-aab2-4e02-b438-da6b6fba500f)

### Simple Dual-Issue Pipeline
![image](https://github.com/user-attachments/assets/9ead48b0-bc36-4049-8557-53de02f0f8ef)

![image](https://github.com/user-attachments/assets/764ddd18-f666-4bae-b9ba-d173e759dcae)

### Another Approach: Split Int/FP
![image](https://github.com/user-attachments/assets/ffb2dd6e-4bec-446f-8690-ae9ca7ab15b3)

### Four-Issue Pipeline (2 integer, 2FP)
![image](https://github.com/user-attachments/assets/23c6ed47-0cdc-450a-b4d9-1eba313d9d50)

### Superscalar Challenges
![image](https://github.com/user-attachments/assets/300de1cd-f9e7-47c5-8b23-6b1d3f13fe12)

## Module 5.2 Challenges of Superscalar Implementation

### Wide Fetch - Sequential Instructions
![image](https://github.com/user-attachments/assets/279a9146-b01c-4592-b05a-8d9edba51043)

The setup allows 1021 and 1022 to be fetched in order, even though in terms of banks they are in reverse order.

### Wide Fetch - Non-Sequential
- Q: Consider a 10 instruction loop body with an 8-issue processor. If 20% of the instructions are branches, what is ILP limited to?

![image](https://github.com/user-attachments/assets/99c0bcca-a79a-498f-b51d-1dc58af3324f)
