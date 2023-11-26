# CMOS Basics
VLSI - very large sca
le integration. Components of VLSI are transistors.

CMOS - complimentary metal oxide semiconductor.

Silicon (group 4) itself is not conducting because there is no flow of electrons. We make impurities in silicon to enable flow of current.

2 types of impurity: n-type (group 5 - additional electron) and p-type (group 3 - remove an electron - hole).

## P-N Junction

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c466c763-4851-45da-bd44-b680c0ea8835)

## CMOS 

### NPN (N-MOS: n-type metal oxide semiconductor)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f979b0e9-12db-46b0-8dcf-27af1fe0b464)

Positive voltage at the gate causes a channel of electrons to form:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/61b00c0e-e304-4b37-b0f0-21a27912d6c6)

The body is the negative terminal or ground and the gate is the positive terminal.

Transistor is like a switch that is controlled by the gate voltage. Threshold voltage (what gate should be at) is usually 0.7V.

### Symbol for NPN CMOS transistor

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ed4c289f-cbb0-4818-9a25-b0685565ddf4)

### Symbol for PNP CMOS transistor

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7cb7a1a8-d2bb-4fc5-820e-c9d890d9bc0b)

Active low means when gate voltage is negative, switch turns on.

Active high means when gate voltage is positive, switch turns on.

### PNP (P-MOS: p-type metal oxide semiconductor)

Negative voltage at the gate causes a channel of holes to form:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d8979d15-ec39-4969-a5b5-fd50ea4b67b7)

### Example: Inverter

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2d294660-6ab9-4b01-bdf6-fc9a93a4b5de)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5ae7d5a3-6678-49cf-be2f-c20ab1672221)

If A = 0, PMOS will be on and NMOS will be off: 

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cb44dec2-ca4b-467e-a9be-b1c729a3b816)

If A = 1, NMOS will be on and PMOS will be off. Output will be connected to ground.

### Example: NAND

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4c088e63-12d6-4427-80a7-2a974c82e4e3)
