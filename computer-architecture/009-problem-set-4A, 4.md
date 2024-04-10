# Problem Set 4A

## Problem 2
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/983c82ea-b167-448f-aae7-011fe1b10849)

a.
Both can take 120 + 16*3 = 168 cycles

b.
L1 cache is smaller and faster. Critical word first allows and processor to get the needed word first and resume execution. Thus, if the L2 cache can get that
word quickly, it will save a lot more time than an L1 cache would.

# Problem Set 4

## Problem 3
What	is	the	reach	of	a	16	entry	fully	associative	TLB	assuming	that	there	are	two	valid	page	sizes,	4KB	and	1MB?

64 KB and 16 MB

## Problem 4
You	are	designing	the	page	tables	for	a	processor	with	a	64-bit	virtual	address	
space.		The	top	bit	is	reserved	and	is	always	set	to	be	zero, therefore	there	is	effective	63-bit	virtual	
address	space. The	processor	has	a	64-bit	physical	address	space.		Assuming	a	page	size	of	8KB,	
construct	a	multi-level	page	table	where	the	different	levels	of	the	page	table	naturally	fit	within	an	8KB	
page.		Assume	that	each	leaf	page	table	entry	needs	a	valid	bit,	a	dirty	bit,	a	kernel/supervisor	bit,	and	
two	software	reserved	bits.		Assuming	that	the	OS	dedicates 10	pages	to	page	table	entries	(any	level)	to	
a	particular	process,	what	is	the	maximum	amount	of	physical	memory	that	can	be	addressed	by	that	
process?		What	is	the	minimum?

Page size is 8KB, thus need 13 bits for offset in virtual address. 1 bit is reserved. So 50 bits for page tables.

Number of pages = 2^63/2^13 = 2^50

Number of page frames = 2^64/2^13 = 2^51

Physical address (64) = page frames (51) + offset (13)
