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

### Problem #2
For	this	problem,	assume	a	VLIW	processor	with	three	integer	units	(X,	Y,	Z),	one	
multiply	unit	(M),	and	two	load-store	units	(LS0,	LS1).		ALU	instructions	have	a	latency of	1,	multiply	
instructions	have	a	latency	of	5,	and	loads	have	a	latency	of	2.		One	branch	can	execute	per	cycle	and	
executes	in	the	Z	pipeline.		The	following	code	has	been	bundled	assuming	the	EQ	scheduling	model.		
What	is	the	value	of	R12,	R13,	and	R14 after	this	code	executes?		Not	changing	register	names,	
reschedule	this	code	assuming	the	LEQ	model.		Why	is	the	LEQ	model	more	flexible?

```
{ADDI	R9,	R0,	9;	ADDI	R10,	R0,	10;}
{ADDI	R6,	R0,	6;	ADDI	R8,	R0,	8; ADDI	R5,	R0,	5;}
{LW	R6,	0(R7);	LW	R8,	4(R7);}
{ADDI	R12,	R6,	1;	ADDI	R13,	R8,	2;}
{MUL	R7,	R6,	R9;}
{MUL	R5,	R8,	R10;}
{LW	R14,	8(R7);} //	Assume	that	8(R7)	contains	the	value	0x1
{ADD	R15,	R16,	R17;}
{ADD	R14,	R14,	R5;}
{SUB	R19,	R18,	R22;}
{ADD	R5,	R7,	R5;}
```
EQ:
```
|       X         |       Y         |       Z      |        M       |        LS0        |      LS1    |   
| ADDI R9,R0,9    | ADDI R10,R0,10  | ADDI R6,R0,6 |                |                   |             |      
| ADDI R8,R0,8    | ADDI R5,R0,5    |              |                | LW R6,0(R7)       |             |   R9 = 9, R10 = 10, R6 = 6
|                 |                 |              |                | LW R8,4(R7)       |             |   R8 = 8, R5 = 5
| ADDI R12,R6,1   |                 |              | MUL R7,R6,R9   |                   |             |   R6 = 0
| ADDI R13,R8,2   |                 |              | MUL R5,R8,R10  |                   |             |   R8 = 0, R12 = 1
|                 |                 |              |                |                   |             |   R13 = 2
|                 |                 |              |                |                   |             |
|                 |                 |              |                |                   |             |
| ADD R15,R16,R17 |                 |              |                |  LW R14,8(R7)     |             |   R7 = 0
|                 |                 |              |                |                   |             |   R5 = 0, R15 = 0
| ADD R14,R14,R5  | SUB R19,R18,R22 | ADD R5,R7,R5 |                |                   |             |   R14 = 0
|                 |                 |              |                |                   |             |   R14 = 5, R19 = 0, R5 = 5
|                 |                 |              |                |                   |             |
```           
After the code executes: R12 = 1, R13 = 2, R14 = 5

LEQ:
```
{ADDI R6, R0, 6; ADDI R8, R0, 8; ADDI R5, R0, 5; LW R14, 8(R7);}  
{LW R6, 0(R7); LW R8, 4(R7); ADDI R12, R6, 1; ADDI R13, R8, 2;}
{ADD R14, R14, R5; ADDI R9, R0, 9; ADDI R10, R0, 10;}
{MUL R5, R8, R10;}
{MUL R7, R6, R9;}
{ADD R15, R16, R17;}
{SUB R19, R18, R22;}
{NOP}
{NOP}
{ADD R5, R7, R5;}
```
LEQ model is more flexible because it is easier to implement prices interrupts.

### Problem #3
Rewrite	the	following	code	assuming	the	instruction	set	has	been	augmented	
with	conditional	move	instructions,	movz	and	movn.		Assume	that	the	branch	misprediction	penalty	is	
10	cycles	and	that	the	branch	to	“forward”	is	random	and	data-dependent.		Does	it	make	sense	to	
predicate?	 Movz	and	movn	have	the	following	semantics:

movz	rd,	rs,	rt						 if	(	R[rt]	==	0	)	then	R[rd]	<- R[rs]

movn	rd,	rs,	rt						 if	(	R[rt]	!=	0	)	then	R[rd]	<- R[rs]

Code	Sequence	for	problem	3:
ADDI	R6,	R0,	1
ADDI	R3,	R0,	50
loop:
LW	R8,	0(R9)
BEQZ	R8,	forward
ADD	R12,	R15,	R8
SUB	R24,	R24,	R12
J	done
forward:
ADDI	R24,	R24,	10
done:
SUBI	R3,	R3,	1
BNEZ	R3,	loop

```
            ADDI R6,R0,1
            ADDI R3,R0,50
            loop:
            LW R8, 0(R9)
            BEQZ R8, forward
ADDI R24,R24,10          ADD R12, R15, R8
SUBI R3,R3,1             SUB R24, R24, R12
BNEZ R3, loop            SUBI R3, R3, 1
                         BNEZ R3, loop
```
Rewrite:
```
ADDI R6,R0,1
ADDI R3,R0,50
loop:
LW R8, 0(R9)
ADDI R27, R24, 10
ADDI R12, R15, R8
SUB  R26, R24, R12
MOVZ R24, R27, R8
MOVN R24, R26, R8
SUBI R3,R3,1
BNEZ R3, loop    
```
