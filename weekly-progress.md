## Week of July 1
- Sunday:
  - PD: 001
- Monday:
  - VER: 00-6
  - SV: 00-4
  - UVM: 00-2
  - EDA Playground: UVM1 Getting Started

## Week of June 24
- Thursday:
  - VER: 00-5
  - SV: 00-3
- Monday:
  - In LC3_tb, figure out how to determine if a branch is predicted in the scoreboard.
  - Find a way to verify the last couple of instructions.

## Week of June 10
- Thursday:
  - Improve the way mem_state is determined in controller. Maybe use a state machine

## Week of June 3
- Saturday:
  - Project: corrected enable_fetch to update at the same time as enable_updatePC. Corrected mem_state logic.
- Monday:
  - Project: My verification helped me find that I implemented second register identification incorrectly, found that I implemented pcout1 incorrectly (when pcselect1 is 3, pcout1 should be 0, not imm5)

## Week of May 27
- Thursday:
  - LC3: Couldn't figure out how to use a sequence library, so had to move on.
- Wednesday:
  - UVM: 00-1
  - VER: 00-4
  - SV: 00-2
- Monday:
  - UVM: 20

## Week of May 13
- Thursday:
  - UVM: 19
- Wednesday:
  - UVM: 18
- Tuesday:
  - UVM: 17
- Monday:
  - UVM: 15, 16

## Week of May 6
- Friday:
  - UVM: 14
- Thursday:
  - UVM: 11, 12, 13
- Wednesday:
  - UVM: 09, 010
- Tuesday:
  - CA: 017
- Monday:
  - UVM: 07

## Week of April 29
- Friday:
  - UVM: 06
  - CA: 018
- Tuesday:
  - UVM: 05
- Monday:
  - CA: 000-15,16
  - UVM: 02

## Week of April 22
- Friday:
  - CA: 016
  - VER: 00-3
  - LC3: Maybe need to add bugs into the code.
- Thursday:
  - CA: 000-13,14; 015
  - LC3: Realized that sr1 and sr2 are determined asynchronously in Execute block
- Wednesday:
  - CA: 000-12; 014
  - SV: 00-1
- Tuesday:
  - CA: 009, 000-9, 010, 011
  - VER: 00-2
  - LC3: Found that there would be 2 dstrans objects in dsmbx in the beginning, shifting the correct order by 1
