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

### Parallel Non-Sequential Fetch
![image](https://github.com/user-attachments/assets/4945a9dd-ba15-421c-b8fc-26317249f6e1)

### Trace Cache
![image](https://github.com/user-attachments/assets/f50bf482-5d98-421b-8bfd-2950360cfd29)

### Trace Cache Example
![image](https://github.com/user-attachments/assets/d68ee3c0-8208-4a41-842c-9bbf6954492e)

### Aside: Multiple-Issue CISC
![image](https://github.com/user-attachments/assets/16114bb2-6f5f-4bd1-85e8-4b0fea5e5c45)

### Wide Decode
![image](https://github.com/user-attachments/assets/98b18d8c-90eb-4bf3-b299-fabf007fd1cc)

### N^2 Dependence Cross-Check
- Q: Describe the N^2 dependence cross-check in superscalar
  
![image](https://github.com/user-attachments/assets/37a71723-87f0-4023-a0a9-88b4aa421efd)

### Superscalar Stalls
- Q1: Describe rigid and fluid methods.
- Q: What is each of their impacts on CPI and the clock.

![image](https://github.com/user-attachments/assets/05cd4a8d-b62a-41a5-9ca3-aa9b7185fb02)

- A1: In rigid, instructions stay together. If one stalls, they both stall.

### Wide Execute
![image](https://github.com/user-attachments/assets/ecba15e3-6bfc-4b22-85d3-0112ed9337b5)

### Wide Memory Access
- Q: What are the 4 options to allow multiple loads/stores? Describe each of them.

![image](https://github.com/user-attachments/assets/3882b927-8931-4e9a-9b55-0af8866f8853)

### N^2 Bypass Network
![image](https://github.com/user-attachments/assets/89330bce-77ab-4110-9372-5470ab36d015)

### Clustering
- Q: What is steering in clustering?

![image](https://github.com/user-attachments/assets/a1c07f0b-8adf-4330-b226-1fe078a37d21)

### Wide Writeback
![image](https://github.com/user-attachments/assets/a3976fea-bc5e-4bb5-8806-dabb3afb6c85)

### Multiple-Issue Implementations
- Q: What are the 4 implementations mentioned here.
  
![image](https://github.com/user-attachments/assets/0702e6da-e285-4edf-9f66-0dd8a1415226)

## Module 5.3 Alternatives: VLIW and EPIC Processors

### VLIW
![image](https://github.com/user-attachments/assets/9607beb4-1d6c-445d-a00e-19bfc4f03e3c)

![image](https://github.com/user-attachments/assets/b4c9a194-2cc5-4037-b675-b216051cbe4b)

### History of VLIW
![image](https://github.com/user-attachments/assets/d03c6f5f-f0cf-4d69-acce-557dc514b2f6)

### Pure and Tainted VLIW
![image](https://github.com/user-attachments/assets/71e27a1d-c241-4fa8-99c6-47f433fdbdff)

### What Does VLIW Actually Buy Us?
![image](https://github.com/user-attachments/assets/5f96df3e-791a-47b5-8bcc-810fa5585306)

### EPIC
![image](https://github.com/user-attachments/assets/1110a34b-ff89-4172-bdfb-7c699157bb5b)

### ILP and Static Scheduling
![image](https://github.com/user-attachments/assets/a9e699e6-053c-4a5a-98a4-38870eda42c0)
