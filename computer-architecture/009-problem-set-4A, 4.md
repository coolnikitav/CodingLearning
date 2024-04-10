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

Assuming byte addressable memory:

Page size = 8KB = 2^13 B

Virtual address space = 2^63 B

Number of entries in a page table if there was 1: 2^63/2^13 = 2^50

Number of frames = 2^64/2^13 = 2^51, so we need 51 bits to address all frames + 5 required bits = 56 bits ~64bits = 8B

Size of that page table = 2^50 * 2^3 = 2^53 B > page size, so num of page tables in last level is 2^53/2^13 = 2^40.

2^40 * 2^3 > 2^13, so second last level will have 2^43/2^13 = 2^30 page tables.

2^30 * 2^3 > 2^13, so third last level will have 2^33/2^13 = 2^20 page tables.

2^20 * 2^3 > 2^13, so fourth last level will have 2^23/2^13 = 2^10 page tables.

2^10 * 2^3 = 2^13, so fifth last level will have 1 table
