# Problem Set 4A

## Problem 1
Don't have access to CACTI

## Problem 2
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/983c82ea-b167-448f-aae7-011fe1b10849)

a.
- Critical word first miss time is 120 cycles.
- Early restart can take 120 cycles if the word is in the first block, 136 if in second block, 152 if in third block, and 168 if in fourth block.
- Without critical word or early restart, the cache processor would need to wait for all 4 blocks, which takes 168 cycles.

b.
L1 cache contributes to average access time more, so it would be more beneficial for it to have early restart/critical word first.

# Problem Set 4

## Problem 3
What	is	the	reach	of	a	16	entry	fully	associative	TLB	assuming	that	there	are	two	valid	page	sizes,	4KB	and	1MB?

16 entries * 1MB/entry = 16MB reach maximum

## Problem 4
You	are	designing	the	page	tables	for	a	processor	with	a	64-bit	virtual	address	
space.		The	top	bit	is	reserved	and	is	always	set	to	be	zero, therefore	there	is	effective	63-bit	virtual	
address	space. The	processor	has	a	64-bit	physical	address	space.		Assuming	a	page	size	of	8KB,	
construct	a	multi-level	page	table	where	the	different	levels	of	the	page	table	naturally	fit	within	an	8KB	
page.		Assume	that	each	leaf	page	table	entry	needs	a	valid	bit,	a	dirty	bit,	a	kernel/supervisor	bit,	and	
two	software	reserved	bits.		Assuming	that	the	OS	dedicates 10	pages	to	page	table	entries	(any	level)	to	
a	particular	process,	what	is	the	maximum	amount	of	physical	memory	that	can	be	addressed	by	that	
process?		What	is	the	minimum?

*Answer is not correct, solution doesn't make sense*

Assuming byte addressable memory:

Page size = 8KB = 2^13 B

V.A. (63 bits) = | 50 idx bit | 13-bit offset |

PTE bits = 2^64 (P.A.S) / 2^13 (page size) + 5 required bits = 56 bits, rounding to 64 bits, or 8B

1-level:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7be1c1bf-0861-47bb-a29f-cb3d4d681c1a)

2-level:

V.A. (63 bits) = | 25 L1 idx bit | 25 L2 idx bit | 13-bit offset |

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1eed9873-865c-4e15-9563-0c12e6bf20cb)

1 * 2^25 * 8 + 2^25*2^25*8 = 

## Problem 5
On a	machine	with	a	software-managed	memory	management	unit	(MMU)	
when	a	TLB	miss	occurs,	what	are	the	possible	reasons?		Does	this	always	result	in	a	buserror/segmentation	fault?		On	a	machine	with	a	hardware	managed	MMU	with	hardware	page-table	
walker,	does	a	page	fault	always	result	in	a	bus-error/segmentation	fault?

- Entry not in TLB.
- This results in a page fault if the data is not found in main memory. If data is found in main memory, TLB is reloaded.
- A page fault is a page fault. What does seg fault have to do with this?

## Problem 6
You	are	executing	on	a	VMIPS	(as	described	on	p.	266	of	H&P5)	architecture	the	
code	below.		Assume	that	the	maximum	vector	length	of	the	architecture	is	128.		Draw	the	pipeline	
diagram	of	this	code	executing	on	a	single-lane	architecture	which	has	an	independent	load	unit,	store	
unit,	multiply	unit,	and	ALU	unit.		Loads	have	a	latency	of	three	cycles	(L0,	L1,	L2),	stores	take	two	cycles	
to	occur	(S0,	S1),	multiplies	take	5	cycles	(Y0,	Y1,	Y2,	Y3,	Y4),	and	ALU	operations	take	two	cycles	(X0,	
X1).		Assume	full	pipelining	of	the	functional	units.		Assume	that	the	pipeline	has	a	dedicated	register	
read	stage	and	a	single	write-stage.		For	the	first	part	of	this	problem,	assume	that	the	architecture	
support	chaining	through	the	register	file,	but	only	has	two read	ports and	one	write	port	on	the	register	
file

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7965852d-cf3f-49e3-9734-8bd17279924d)

We only draw the vector pipeline because the scalar pipeline is usually decoupled.

Answer:
```
LV V1, R4          | F D R L0 L1 L2 W
                   |       R  L0 L1 L2 W
                   |          R  L0 L1 L2 W
                   |             R  L0 L1 L2 W
                   |                R  L0 L1 L2 W
                   |                   R  L0 L1 L2 W
MULVS.D V3, V1, F2 |   F D D  D  D  D  D  R  Y0 Y1 Y2 Y3 Y4 W           
                   |                         R  Y0 Y1 Y2 Y3 Y4 W
                   |                            R  Y0 Y1 Y2 Y3 Y4 W
                   |                               R  Y0 Y1 Y2 Y3 Y4 W
                   |                                  R  Y0 Y1 Y2 Y3 Y4 W
                   |                                     R  Y0 Y1 Y2 Y3 Y4 W
LV V2, R5          |     F D  D  D  D  D  D  D  D  D  D  D  D  D  R  L0 L1 L2 W 
                   |                                                 R  L0 L1 L2 W
                   |                                                    R  L0 L1 L2 W
                   |                                                       R  L0 L1 L2 W
                   |                                                          R  L0 L1 L2 W
                   |                                                             R  L0 L1 L2 W
ADD V4, V3, V2     |       F  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  R  X0 X1 W
                   |                                                                      R  X0 X1 W
                   |                                                                         R  X0 X1 W
                   |                                                                            R  X0 X1 W
                   |                                                                               R  X0 X1 W
                   |                                                                                  R  X0 X1 W
SV R6, V4          |          F  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  D  R  S0 S1 W
                   |                                                                                        R  S0 S1 W
                   |                                                                                           R  S0 S1 W
                   |                                                                                              R  S0 S1 W
                   |                                                                                                 R  S0 S1 W
                   |                                                                                                    R  S0 S1 W
```
Solution matches the answer.

## Problem 7
Redo	the	above	pipeline	diagram	(Problem	#6)	assuming	that	the	pipeline	has	a	
write	port	and	two	read	ports	per	functional	unit	and	that	the	architecture	has	two	lanes	(two	
duplicates	of	all	functional	unit	resources).

Answer:
```
LV V1, R4          | F D R L0 L1 L2 W
                   |       R  L0 L1 L2 W
                   |          R  L0 L1 L2 W
                   |     R L0 L1 L2 W
                   |        R L0 L1 L2 W
                   |          R  L0 L1 L2 W
MULVS.D V3, V1, F2 |   F D D  D  R  Y0 Y1 Y2 Y3 Y4 W           
                   |                R  Y0 Y1 Y2 Y3 Y4 W
                   |                   R  Y0 Y1 Y2 Y3 Y4 W
                   |             R  Y0 Y1 Y2 Y3 Y4 W
                   |                R  Y0 Y1 Y2 Y3 Y4 W
                   |                   R  Y0 Y1 Y2 Y3 Y4 W
LV V2, R5          |     F D  D  D  D  D  D  D  R  L0 L1 L2 W 
                   |                               R  L0 L1 L2 W
                   |                                  R  L0 L1 L2 W
                   |                            R  L0 L1 L2 W
                   |                               R  L0 L1 L2 W
                   |                                  R  L0 L1 L2 W
ADD V4, V3, V2     |       F  D  D  D  D  D  D  D  D  D  D  R  X0 X1 W
                   |                                           R  X0 X1 W
                   |                                              R  X0 X1 W
                   |                                        R  X0 X1 W
                   |                                           R  X0 X1 W
                   |                                              R  X0 X1 W
SV R6, V4          |          F  D  D  D  D  D  D  D  D  D  D  D  D  R  S0 S1 W
                   |                                                    R  S0 S1 W
                   |                                                       R  S0 S1 W
                   |                                                    R  S0 S1 W
                   |                                                       R  S0 S1 W
                   |                                                          R  S0 S1 W
```
Solution:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f4a17e9-8f10-4edc-9700-ced1faa6f5a9)

## Problem 8
Do	GPUs	have	vector	length	registers?		Describe	how	GPUs	handle	the	case	
where	two	elements	in	a	vector	of	data	need	different	processing.

GPUs do not have VLRs.Instead, they pack a vector into SIMD style operations.

When 2 elements of data in a vector need different processing, operations are masked using a vector mask. This is a form of predication.
