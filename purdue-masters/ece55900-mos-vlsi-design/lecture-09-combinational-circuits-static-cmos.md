# Combinational Circuits: Statis CMOS

## Combinational vs Sequential Logic
![image](https://github.com/user-attachments/assets/7ec6e1d0-254c-416e-9d6f-6354e5f6f131)

## Static vs Dynamic Circuits
![image](https://github.com/user-attachments/assets/166c0d3d-ec84-46d2-b58f-fee39cd974f9)

## Static CMOS
![image](https://github.com/user-attachments/assets/707db3d7-07cb-42f2-a776-5667ab8d2010)

## Why NMOS For PDN And PMOS For PUN?
- Q: Explain why we use NMOS for PDN and not PMOS. Same for PUN.

![image](https://github.com/user-attachments/assets/27cffdbf-00e9-45fe-b847-d1e3adfbe5bc)

## Primitive Connections For PDN: Series and Parallel
![image](https://github.com/user-attachments/assets/ffccc188-05f4-49ba-aba3-3852d04fa4f8)

## Primitive Connections For PUN: Series and Parallel
![image](https://github.com/user-attachments/assets/acb8b9c2-64d2-4a05-878a-568e60e5ad99)

## Static CMOS Examples
![image](https://github.com/user-attachments/assets/7aef7e8e-cd8d-4cb9-aae4-ae935d213efd)

- Q: Scroll down a little bit to see the equation. Draw the schematic for it.
  
![image](https://github.com/user-attachments/assets/9b9bf8a8-7650-4a6e-9d2c-2aee47e19e49)

- Q: Scroll down a little bit to see the equation. Draw the schematic for it.
  
![image](https://github.com/user-attachments/assets/638d9650-dcb2-43a3-ad9c-c5ffb6ac0d4b)

## Layouts Of The Static CMOS Gaters: Stick Diagrams
- Q: Draw the stick diagrams for the inverter and the NAND gate.

![image](https://github.com/user-attachments/assets/15fd1166-f623-43ba-be6e-c37f328096b4)

## Layout: OAI21
![image](https://github.com/user-attachments/assets/d9b72ba1-ffa9-437c-961e-d24898b7be09)

## Layouts: Maximize Contact Sharing Using Euler's Rule
- Q: What is Euler's rule?

![image](https://github.com/user-attachments/assets/a6ec6c88-ee74-422e-b812-9374e514cd94)

## Euler's Rule For OAI22
![image](https://github.com/user-attachments/assets/cbb9a08c-f5ea-4583-b5f5-a49e095e84c8)

## Layouts: Multi-Fingered Transistors
![image](https://github.com/user-attachments/assets/45fac8e2-8b01-420e-a300-4daa063a8490)

## CMOS Properties
![image](https://github.com/user-attachments/assets/c906ca01-ed52-491d-88c4-4b7beea8abc8)

## Switch Delay Model
![image](https://github.com/user-attachments/assets/708c5e87-a9b8-45f2-8fb6-22a3b4b951bc)

![image](https://github.com/user-attachments/assets/e33f584b-ee27-4435-96e1-e6ca101c875d)

## Input-Dependent Delay: NAND2
![image](https://github.com/user-attachments/assets/20b75613-4f55-4659-aa41-a205fb49b33a)

![image](https://github.com/user-attachments/assets/c16ae4be-76ee-4093-bf17-70cc281951cd)

![image](https://github.com/user-attachments/assets/dc9cd638-5cc8-41c3-9cbf-4021f9e161d3)

![image](https://github.com/user-attachments/assets/45cf3a27-7a47-4ef9-b398-dc5eb77b3406)

![image](https://github.com/user-attachments/assets/9adb92ab-07d9-4389-a149-40f6a2d435a9)

![image](https://github.com/user-attachments/assets/03da5e27-e5f2-4863-ac7e-163089b041bc)

![image](https://github.com/user-attachments/assets/057fd10b-301f-442d-8403-0c5bdcac5128)

## Input-Dependent Delay: NAND2 (Input a closer to output)
![image](https://github.com/user-attachments/assets/0ab88701-07fd-4182-b4df-ba42c736fe8f)

## Transistor Sizing For Equal "Worst-Case" Rise and Fall Delays
![image](https://github.com/user-attachments/assets/ee7c5219-aafb-43d5-946c-e9470241e8cb)

- Note: for the parallel network, we only consider one of the transistors connected because that will give us the worst-case scenario.

![image](https://github.com/user-attachments/assets/6daf6d67-a821-4d80-8fa5-3da53600a9bb)

![image](https://github.com/user-attachments/assets/b91c0d1b-a000-424e-bcd4-c369d0ceaf7c)

## Dependance of Delay on Fan-In
![image](https://github.com/user-attachments/assets/2f2796bf-4112-49a3-9154-6ed9507d23ae)

![image](https://github.com/user-attachments/assets/9e3c90f4-0869-4b98-8e75-da156a7ffd99)

![image](https://github.com/user-attachments/assets/be90b0c1-a1c3-413c-9e04-3703972816d2)

## Dependence of Delay on Fan-Out
![image](https://github.com/user-attachments/assets/9836eb28-f1c6-4475-8c89-7dbd21115fb1)

## Increasing Speed: Design Technique 1
- Q: What is the first technique? What are the trade-offs?

![image](https://github.com/user-attachments/assets/a089eb7a-72e6-4468-97d7-845d15d5f2f8)

## Increasing Speed: Design Technique 2
- Q: What is the second technique?

![image](https://github.com/user-attachments/assets/ad83049a-fb54-488a-a821-4e05cf68bb4a)

Note: critical path: the longest path

## Increasing Speed: Design Technique 3
- Q: What is the third technique?

![image](https://github.com/user-attachments/assets/1109334f-d7c0-47e9-8b73-6fbc502265a8)

## Increasing Speed: Design Technique 4
![image](https://github.com/user-attachments/assets/d2ab5dd0-8812-4ccb-89aa-b61ffbc09f31)

## Recall: Inverter Delay
![image](https://github.com/user-attachments/assets/22df778d-e043-47ab-829e-b04d93aab7ac)

## Simplifying Assumptions
![image](https://github.com/user-attachments/assets/5a9b46f0-af34-49e2-95bc-d62071d94bd6)

## Generalization Beyond Inverters
- Q: What is the equation for delay for a logic gate?

![image](https://github.com/user-attachments/assets/b4c2bfdf-10e6-4c4d-a5e5-8eecc4f83d07)

## Parasitic Delay or Intrinsic Delay
![image](https://github.com/user-attachments/assets/3e790222-bc7b-423c-b0f9-1b2b6122bf80)

## Recipe for Parasitic Delay
![image](https://github.com/user-attachments/assets/0f51ec21-4048-4ee8-82a3-bdce841d2244)

## Example: Parasitic Delay Or Intrinsic Delay
![image](https://github.com/user-attachments/assets/95b1439c-9230-46a6-8512-df9122376544)

Note: mu = 2 means mobility of electrons is twice than of holes

![image](https://github.com/user-attachments/assets/48d1e9af-3b3c-4350-88a5-7b24602fcbf8)

![image](https://github.com/user-attachments/assets/c0ae406b-988d-4d71-9df5-0ad277240e72)

## Parasitic Delay or Intrinsic Delay
![image](https://github.com/user-attachments/assets/180d3290-54a1-4530-b403-a936982ceed3)

## Logical Effort
- Q: How is logical effort calculated?

![image](https://github.com/user-attachments/assets/f1265002-5e3d-4936-b52f-d6ff03a6de25)

![image](https://github.com/user-attachments/assets/f7ecf75b-cad0-4558-9d97-f75a741fafe3)

## Recipe for Logical Effort
![image](https://github.com/user-attachments/assets/925d370d-93cb-498a-81fc-571261805ca5)

![image](https://github.com/user-attachments/assets/4fd0774a-1965-400a-ae65-caf8dd0583dd)

## Logical Effort
![image](https://github.com/user-attachments/assets/1fd4a81d-607b-4c5d-9b86-350792669389)

## Dependence of Delay on Fan-Out
![image](https://github.com/user-attachments/assets/2ee77622-821a-4fef-91bf-bc8057e65bd1)

## Sizing Considering Equalization of Resistance vs Equalization of Input Capacitance
![image](https://github.com/user-attachments/assets/0b4d1524-346d-440b-a445-cd0c7f556e79)

![image](https://github.com/user-attachments/assets/6b920846-9edc-402a-ace6-83ee3fc11830)

Note: resistance has increased on the right

![image](https://github.com/user-attachments/assets/40bf7b1f-c667-4523-8401-73d7440918ba)

![image](https://github.com/user-attachments/assets/d7028b3d-3624-40c4-a683-802a8d6822ec)

## Delay Optimization For a Path
![image](https://github.com/user-attachments/assets/32313d86-142f-4379-a73e-d716bd37bae9)

## Definitions
![image](https://github.com/user-attachments/assets/587ca3e0-b82f-45b2-8cc1-35a461641e8f)

## Fanout And Branching
![image](https://github.com/user-attachments/assets/e52a2edf-18cb-4e57-8058-099c8e48ec3b)

## Procedure To Minimize Path Delay
![image](https://github.com/user-attachments/assets/8841b92e-ff2d-4af3-b260-6105980f6f8c)

## Example 1
![image](https://github.com/user-attachments/assets/a7488b98-0149-42a5-ac2f-1fbb3016e3e4)

![image](https://github.com/user-attachments/assets/7d6216b3-b3e9-4c94-9eb3-6761f0dbfae6)

![image](https://github.com/user-attachments/assets/989c8d14-5398-4c33-a1b6-3061ce731d87)

![image](https://github.com/user-attachments/assets/3aeeb556-dee2-4dcb-b809-75bc5d4c1ccd)

## Example 2
![image](https://github.com/user-attachments/assets/c726625f-c44f-47f6-8769-3809ef982d06)

![image](https://github.com/user-attachments/assets/dcb2259a-e65f-4403-adc9-dfe1c0d05f2a)

![image](https://github.com/user-attachments/assets/c9af08da-137e-4a5e-a935-91f47fbbc398)

![image](https://github.com/user-attachments/assets/fe695cad-7713-4940-bebc-9c3053268d09)
