# MOSFETs

## MOSFETs: Device Structure
- Q: Draw a diagram of an n-MOSFET? When is it on? When is it off? Where is the current flowing from and to?
- Q: Draw a diagram of an p-MOSFET? When is it on? When is it off? Where is the current flowing from and to? 
  
![image](https://github.com/user-attachments/assets/08510c29-ce29-4b74-b6d8-d2191fc8d6ac)

![image](https://github.com/user-attachments/assets/56a74cb2-af09-4b50-a48d-2c6c87df1c33)

- Substrate = body terminal
- n-MOSFET has electrons flowing
- p-MOSFET has holes flowing

## Band Diagrams: N-MOSFET
- Q: What is the equation for energy in this context?
- Q: What is DIBL?
  
![image](https://github.com/user-attachments/assets/999e1753-e71b-4ba3-8b6e-5581545b691e)

![image](https://github.com/user-attachments/assets/08254a91-80a4-4638-a8b3-5559aae26dc2)
- The leakage current increases due to DIBL.

We want the gate voltage to lower the barrier when the device is turned on:

![image](https://github.com/user-attachments/assets/041de298-006c-4520-85ba-37c40117c49a)

- Q1: Where does the fermi level move when you dope a semiconductor with holes to make it p-type? n-type?
- Q2: What are we looking at? What do the lines mean? What does the rectangle/rhombus mean?
![image](https://github.com/user-attachments/assets/2f551778-bb1e-4807-a9f6-d8304586b346)

- A1: Fermi level will move closer to the valence band. n-type is the opposite: towards the conduction band.

- Q: What happens to the previous band diagram when Vgs > 0? Does it become more n-type or p-type? Why?

![image](https://github.com/user-attachments/assets/41f5b444-a74a-412e-b7cf-e573bf9ebb12)

![image](https://github.com/user-attachments/assets/4314428e-c283-42d4-91cf-32db1d1e91a4)

## Threshold Voltage (Vth)
- Q: At Vgs = Vth, what is the relationship between surface and bulk?
- Q: At threshold, what is the relationship between psi S and psi B?
- Q: What is the equation that describes Vgs (ideal and non ideal)?
  
![image](https://github.com/user-attachments/assets/a3f1ae80-d374-4d7e-9e1d-0c5d81b035d8)

![image](https://github.com/user-attachments/assets/9458e601-a88d-4ef7-99ea-94fc92fa6277)

![image](https://github.com/user-attachments/assets/d2a0cbf3-98b5-46c1-aa06-4bc0d1fc006a)

## Body Effect (Non-Zero Source-To-Body Voltage)
- Q1: What should be the voltage of the body of an n-mosfet? What about a p-mosfet? Why?
- Q: How does relationship between surface and bulk potential change if we account for the body effect?

![image](https://github.com/user-attachments/assets/34d5751f-9f11-4ee0-b840-d92dfabf1860)

- A1: Most negative, to make sure the diode in the pn junction is always reverse biased (off). Most positive

![image](https://github.com/user-attachments/assets/357382dd-4f47-46a9-ac9d-97733e7b62bb)

## Threshold Voltage With Body Effect (NMOS)
- Q: Write the equation for the threshold voltage without and with body effect.

![image](https://github.com/user-attachments/assets/b3a1e1a5-1b16-425d-95a2-a9209e09700f)

## Sub-Threshold Characteristics (Vgs < Vth)
- Q: How to express surface potential in terms of oxide capacitance, substrate capacitance, and Vgs?
- Q: What is the body factor? What is the equation for it?
- Q1: What should the voltage be set to in order to completely lower the barrier?

![image](https://github.com/user-attachments/assets/b830c526-b9f7-4c23-89e0-2815d086d542)

- A1: The threshold voltage, which corresponds to Eb.
  
The number of electrons that can be injected over the barrier are exponentially related to the negative of the barrier. If the barrier is high, the number of electrons that can be injected is exponentially reduced. If the barrier is lowered, the number of electrons that can be injected will exponentially increase.

psi S corresponds to Vgs
