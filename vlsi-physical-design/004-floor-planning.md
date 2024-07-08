# Floor-planning
### Partitioning

Q: Draw a stick diagram for a CMOS inverter.

![image](https://github.com/coolnikitav/learning/assets/30304422/baf9f333-007e-4871-b32a-fc70636a57e1)

### Terminologies
![image](https://github.com/coolnikitav/learning/assets/30304422/7aac1af5-9a13-4fc1-951b-9820e4237f07)

Side rows, manufacturing grid

![image](https://github.com/coolnikitav/learning/assets/30304422/f554aed7-44ba-44e2-962d-e7eb45b2e52a)

![image](https://github.com/coolnikitav/learning/assets/30304422/edd26867-d973-4561-ae9c-8b9a66bdbd48)

# Floorplanning and IO placement
Q: What are the different types of ports?
Q: What is NDR and what signal typically uses it and why?
Q: What are blockeages?
Q: Define good port placement.

![image](https://github.com/coolnikitav/learning/assets/30304422/ccadb597-3538-467a-976f-f80b71332136)

Data cannot be in a bidirectional port. Those ports are usually used for power.

NDR - non default rule. Clock usually doesnt use default spacing because it switches frequently, creaing lots of noise.

![image](https://github.com/coolnikitav/learning/assets/30304422/94708162-5206-449f-85ba-1fed28b6db84)

Blockages block empty area without ports, so ports arent applied there.

![image](https://github.com/coolnikitav/learning/assets/30304422/51bb0e99-123e-49e3-af64-f9a5f4af5a50)

# Marco Placement and Floor-Planning
Q: What are macros?
Q: What are the macro placement tips?

![image](https://github.com/coolnikitav/learning/assets/30304422/e57289f6-d4ae-4d2a-a8fe-c053030af824)

![image](https://github.com/coolnikitav/learning/assets/30304422/55d174cf-9812-48df-8657-91e3b587f177)

DFM - design for manufacturability

![image](https://github.com/coolnikitav/learning/assets/30304422/addb8282-ca56-458d-82fd-58e1eb09c897)

# Macro placement guidelines and floor-planning
Q: What are some more macro placement guidelines?

![image](https://github.com/coolnikitav/learning/assets/30304422/5ec76f7c-f3c9-4d44-bf5b-dc86f96c9a26)

Criss cross of nets is not preferred, more straight lines means better placement

# Macro channel spacing estimation and floor-planning
Q: How to calculate channel length between 2 macros?

![image](https://github.com/coolnikitav/learning/assets/30304422/28d92083-c489-41d7-b157-25730a3606cf)

![image](https://github.com/coolnikitav/learning/assets/30304422/0acd6cab-d179-4b9b-9ef6-3ef6ab4d6b4c)

If there are 6 routing layers, we only count 3 because we will either use vertical or horizontal layers.

We also need to account for 1 more ground and 1 more power pin, additing more to channel length.

![image](https://github.com/coolnikitav/learning/assets/30304422/9c07124d-4311-4bfd-b69c-43de393a3e41)
