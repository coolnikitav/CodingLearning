# Physical Design Inputs Overview
Q: What are the inputs provided?

![image](https://github.com/coolnikitav/learning/assets/30304422/9f7070d2-865a-498c-9f11-a02898440d4a)

# Netlists
Q: What is a netlist?

Netlist defines logical functionality and connectivity of the design. File extensions are .v and .vg.

Unsynthesized netlist is also called as RTL code.

Unsynthesized netlist is technology independent. Synthesized netlist is technology dependent.

# Timing library
Q: How do we know the delay through a gate in a logic path?
Q: What does NLDM stand for? What does NLDM propagation delay depend on?
Q: What does CCS propagation delay depend on?

We know the delay from the library.

NLDM = non linear delay model

![image](https://github.com/coolnikitav/learning/assets/30304422/53d7e48d-766b-404b-9c91-207c378eba55)

NLDM propagation delay depends on transition time and load capacitance.

CCS propagation delay depends on transition time, load capacitance, and time at which you are sampling the data.

![image](https://github.com/coolnikitav/learning/assets/30304422/cd50f3a5-b88f-44a6-81e1-af9f201aa04f)

# LEF File
Q: What does LEF stand for? What does it hold?

CMOS Inverter Layout:

![image](https://github.com/coolnikitav/learning/assets/30304422/bf4fb243-5fc7-4060-b52c-5d5e68c4a0dc)

Library exchange format - has the layout view of all the cells

![image](https://github.com/coolnikitav/learning/assets/30304422/6796080f-d484-49cb-8016-bbda9500f091)

# Constraints file
Q: What are the 2 main groups of constraints? What types of constraints does each of these groups have?

Design rule constraints and optimization constraints.

![image](https://github.com/coolnikitav/learning/assets/30304422/8d8b859f-2212-41ce-aadf-8bfe02d2eb92)

![image](https://github.com/coolnikitav/learning/assets/30304422/785ff48d-edd5-44b9-ade1-ccca53e9ca74)

# Technology File
Q: What does the technology file have in it?

tech file is technology dependent

![image](https://github.com/coolnikitav/learning/assets/30304422/08a9a853-02c3-4044-806e-bcd5cd2103b5)

![image](https://github.com/coolnikitav/learning/assets/30304422/3ddf59c0-6bc6-4bb8-b1d4-95b1a781a8e9)
