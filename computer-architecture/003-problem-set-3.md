# Computer Architecture ELE475
## Problem Set #3

### Problem #1
For	this	problem,	assume	a	VLIW	processor	with	three	integer	units	(X,	Y,	Z),	one	
multiply	unit	(M),	and	two	load-store	units	(LS0,	LS1).		ALU	instructions	have	a	latency	of	1,	multiply	
instructions	have	a	latency	of	5,	and	loads	have	a	latency	of	3.		One	branch	can	execute	per	cycle	and
executes	in	the	Z	pipeline.		For	the	following	code,	fully	unroll	and	software	pipeline	the	code	to	improve	
performance.		Show	the	prolog	and	epilog	code.		Feel	free	to	use	more	registers,	reorder	code,	and	
rename	registers	for	performance.		What	high	order	functionality	does	the	function	implement?		What	
is	the	average	rate	of	multiplies	per	cycle	in	the	middle	of	the	loop?
```
//R0	is	hardwired	to	zero
//R31	is	the	link	register
//R1	contains	pointer	to	input	array	(elements	are	word	sized)
//R2	contains	pointer	to	output	array	(elements	are	word	sized)
//				(Output	array	is	larger	than	input	array)
//R3	contains	the	size	of	the	input	array	in	words
function:
ADDI	R16,	R0,	0x456
ADDI	R17,	R0,	0x789
ADDI	R18,	R0,	0x901
ADD	R4,	R0,	R0
ADD	R5,	R0,	R0
loop:
LW	R6,	0(R1)
MUL	R8,	R4,	R16
MUL	R9,	R5,	R17
MUL	R10,	R6,	R18
ADDI	R1,	R1,	4
SUBI	R3,	R3,	1
ADD	R8,	R8,	R9
ADD	R8,	R8,	R10
ADD	R4,	R5,	0
ADD	R5,	R6,	0
SW	R8,	0(R2)
ADDI	R2,	R2,	4
BNEZ	R3,	loop
MUL	R8,	R4,	R16
MUL	R9,	R5,	R17
ADD	R8,	R8,	R9
SW	R8,	0(R2)
ADDI	R2,	R2,	4
ADD	R4,	R5,	0
MUL	R8,	R4,	R16
SW	R8,	0(R2)
JR	R31
```
```
loop:
LW	R6,	0(R1)
MUL	R8,	R4,	R16
MUL	R9,	R5,	R17
MUL	R10,	R6,	R18
ADDI	R1,	R1,	4
SUBI	R3,	R3,	1
ADD	R8,	R8,	R9
ADD	R8,	R8,	R10
ADD	R4,	R5,	0
ADD	R5,	R6,	0
SW	R8,	0(R2)
ADDI	R2,	R2,	4
BNEZ	R3,	loop
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/20a4bd4d-e943-40e1-86dc-570cb27ab2ea)
