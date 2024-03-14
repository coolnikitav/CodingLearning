# Verification Fundamentals

## Understanding Verification Plan
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a029c5d0-dd08-4c26-bd72-b84948de29cf)

Look at the spreadsheet and then create a table:
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ab824029-7035-4bb0-a01f-feb725ed65e7)

## Directed Test vs Constraint Random Test

### Directed Test
Take a test from your test plan. Test your DUT. Analyze the results. Then take the next test, apply it, and analyze the results.

Its handy if there are a limited number of test cases and the design is simple.

### Constrained Random Test
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f44bf5fa-0a56-4172-b3e2-d7a79871795e)

FC - functional coverage. VP - verification plan.

## Layered Architecture
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/56bf9b49-d141-448a-b334-95f1e7bff17a)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f2b041b0-0bfd-436f-bfcd-e75a61984005)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/33d7afd1-11b8-4d9b-8b04-801cc1ce2d42)

## Individual Components of TB

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5a99e62b-e3c3-460e-9724-b99f7323ef09)

Transaction - contain variables for all the inputs/outputs ports present in DUT to share among classes.

Generator - generate random stimulus and send it to driver using IPC (inter process comm).

Driver - receive stimulus from generator and trigger respective signals of DUT with help of Interface.

Monitor - receive response from DUT and send it to scoreboard using IPC.

Scoreboard - compare response of DUT with expected/golden data.

Environment - hold generator, driver, monitor, scoreboard together.

Test - hold environment and control simulation process.
