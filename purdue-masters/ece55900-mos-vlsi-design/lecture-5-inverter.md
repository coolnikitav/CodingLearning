# Inverter: DC Characteristics

## MOSFETs: Regions Of Operations
- Q: How may the mosfet be modeled in each region of operation?
  
![image](https://github.com/user-attachments/assets/791401fe-3eef-47c3-a2d9-856c9fbed228)

## MOSFETs: Current Equations In Super-Threshold Region
![image](https://github.com/user-attachments/assets/edfe4f85-8be2-4d7d-af0e-fa2a67b298f8)

## Inverter Topologies With Resistive Loads
- Q: Draw inverter with 1 resistor and 1 nmos.
- Q: Draw an NMOS-inverter with NMOS saturated load
- Q: Draw a PMOS-inverter with PMOS saturated load
- Q: How do we tell that they are always in saturation?

![image](https://github.com/user-attachments/assets/4c0ca02d-706e-49db-90d5-9fba11c4df64)

## CMOS Inverter
- Q: Draw the CMOS inverter schematic.

![image](https://github.com/user-attachments/assets/102562da-06db-44e6-918f-72a26fbf5823)

# DC Characteristics

## Voltage Transfer Characteristics
![image](https://github.com/user-attachments/assets/efd59880-a2ad-453a-a86c-17e8ada0a38b)

## Definitions
- Q: What is a unity gain point?

![image](https://github.com/user-attachments/assets/90ef7cea-156a-4866-84e3-44ebaf36b2b2)

## Noise Margins
- Q: What is the equation for noise margin high and noise margin low? Explain why they are like that.
  
![image](https://github.com/user-attachments/assets/867cbd13-5029-4456-8939-713f6eab9996)

## VTC For An Inverter With A Resistive Load: Load Line Method
![image](https://github.com/user-attachments/assets/498a423f-ff91-40c8-a737-b84368acf8e1)

- Q: As R_L is increasing, how is the output curve changing?
  
![image](https://github.com/user-attachments/assets/e23f2f51-b5cd-45a3-8c92-58c229a1123f)

## VTC For A Pseudo-NMOS Inverter: Load Line Method
- Q: How do Wp and Lp affect the current:
![image](https://github.com/user-attachments/assets/86a1eed7-ab5f-4ff9-b2ee-ebb0cf235e6c)

- Q1: Is the V_OL of this inverter smaller or larger than the linear one?
  
![image](https://github.com/user-attachments/assets/a30e9946-6810-4566-a3c2-3e888b1e6ca3)

- A1: Smaller

## VTC For A CMOS Inverter: Load Line Method
![image](https://github.com/user-attachments/assets/064fd49d-6974-498b-a60b-ac0feb9b9223)

![image](https://github.com/user-attachments/assets/c20c59c5-a3c2-47b8-8c06-ba90a4b9780d)

## Obtaining VTC And Metrics Of Interest: Analytical Method
![image](https://github.com/user-attachments/assets/99a2061e-a2a5-4351-9293-22636f8412b9)

## VTC For An Inverter With a Resistive Load: V_OH
- Q: Derive the equation for V_OH for the inverter with resistive load.
  
![image](https://github.com/user-attachments/assets/b44d7e40-b838-4951-9903-394ec46c484a)

## VTC For An Inverter With a Resistive Load: V_OL
- Q: Derive the equation for V_OL for the inverter with resistive load.
  
![image](https://github.com/user-attachments/assets/a08e3c4c-a1e6-4c11-b723-7775a450f559)

## VTC For An Inverter With a Resistive Load: V_M
- Q: Derive the equation for V_M for the inverter with resistive load.

![image](https://github.com/user-attachments/assets/afdac065-e53f-44b4-a4bf-52b12f664872)

## Design For V_OL
![image](https://github.com/user-attachments/assets/6f3effb2-d957-4701-870c-5f5eed4aa74d)

## CMOS Inverter: Analytical Method
- Q: Do the exercise for V_OL.

![image](https://github.com/user-attachments/assets/29e1629a-0556-4b9d-b597-5080630499bf)

## CMOS Inverter: Analytical Method - Pinch-Off Based Saturation
![image](https://github.com/user-attachments/assets/9b32747e-0a0d-4713-8df6-fc7c12da9ef9)

## CMOS Inverter: Analytical Method - Velocity Saturation
![image](https://github.com/user-attachments/assets/a0683917-0d24-47f4-81a2-4b4a183bad6b)

## CMOS Inverter: Sizing For V_M
- Q1: What is our most desirable value of V_M?

![image](https://github.com/user-attachments/assets/c83deedc-0d31-4af7-a345-d86f4e0e605e)

- A1: Vdd/2

## CMOS Inverter: Sizing For V_M = V_DD/2
![image](https://github.com/user-attachments/assets/33f6a738-e15a-47a6-8338-68a3a35f2243)

## Change In VTC With Sizing And/Or Process Variations
- Q: How does VTC curve shift with a strong PMOS, weak NMOS? What about strong NMOS, weak PMOS?

![image](https://github.com/user-attachments/assets/45577c44-ed1c-476b-81a3-aaf86985de9e)

## Determining V_IH And V_IL: CMOS Inverter
![image](https://github.com/user-attachments/assets/ef9324aa-8741-4933-8e3a-2d26b79645dc)

## Inverter Gain
![image](https://github.com/user-attachments/assets/9a5ddb97-91b1-4517-899f-d37480eabd1e)

## Inverter Gain As A Function Of Vdd
- Q: Draw the Vout vs Vin curve you would see at Vdd = 2.5, 1.5, 0.5, 0.2, 0.1, 0.05V

![image](https://github.com/user-attachments/assets/701eab56-5c84-48c1-9d64-653f82b596ea)

You can make an inverter even if the NMOS or a PMOS are in the off state. At that point you are talking about "which device is more on/off".
