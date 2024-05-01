# Problem Set #5

## Problem #1: 3.13
Skip this.

## Problem #2
Assume	that	your	architecture	has	a	test-and-set	instruction	as	its	only	atomic	
primitive.		Implement	atomic	compare-and-exchange	out	of	the	test-and-set	primitive.

Answer:
Test&Set (m), R: if M[m] is 0, set it to 1

Compare&Swap(m), Rt, Rs: if Rt is in M[m], then put Rs in M[m] and Rt into old Rs

We have Rt in M[m] and Rs we want to swap it with.

How can we set M[m] to Rs if we can only set it to 1 with Test&Set?


## Problem #3
List	the	possible	sequentially	consistent	outcomes	for	the	variables	i	and	j	after	
the	completion	of	executing	the	three	threads	T1,	T2,	and	T3.		Assume	that	all	threads	begin	executing	
after	‘i’	has	been	set	to	9	and	‘j’	is	set	to	10.
i = 9, j = 10
```
T1:
ADDI	R1,	R0,	30
SW	R1,	0(i)
LW	R2,	0(j)
SW	R2,	0(j)

T2:
ADDI	R5,	R0,	99
LW	R6,	0(j)
ADD	R7,	R5,	R6
SW	R7,	0(j)

T3:
ADD	R8,	R0,	100
SW	R8,	0(i)

```
1:
```
ADDI R1, R0, 30   ; R1 = 30
SW R1, 0(i)       ; i = 30
LW R2, 0(j)       ; R2 = 10
SW R2, 0(j)       ; j = 10
ADDI R5, R0, #99  ; R5 = 99
LW R6, 0(j)       ; R6 = 10
ADD	R7,	R5,	R6    ; R7 = 109
SW	R7,	0(j)      ; j = 109
ADD	R8,	R0,	100   ; R8 = 100
SW	R8,	0(i)      ; i = 100
; Outcome: i = 100, j = 109
```
3:
```
ADD	R8,	R0,	100    ; R8 = 100
SW	R8,	0(i)       ; i = 100
ADDI	R5,	R0,	99   ; R5 = 99
LW	R6,	0(j)       ; R6 = 10
ADD	R7,	R5,	R6     ; R7 = 109
SW	R7,	0(j)       ; j = 109
ADDI	R1,	R0,	30   ; R1 = 30
SW	R1,	0(i)       ; i = 30
LW	R2,	0(j)       ; R2 = 109
SW	R2,	0(j)       ; j = 109
; Outcome: i = 30, j = 109
```

## Problem #4
You	are	writing	a	multi-threaded	program	that	will	count	the	number	of	
occurrences of	a	value	in	an	array.		The	values	in	the	array	are	between	0	and	1023.		In	effect,	you	will	
be	building	a	histogram.		Assume	that	the	list	of	numbers	is	very	large,	on	the	order	of	gigabytes	large.		
Extend	the	following	program	such	that	100	threads	(processors)	can	execute	on	the	program	
concurrently.		Assume	a	sequentially	consistent	memory	model.		Add	P()	and	V()	semaphores	where	
appropriate	and	add	any	storage	needed	for	the	semaphores.		Explain	why	the	speedup	of	such	a	
solution	may	not	be	100x. Note	that	the	output	lock	array	is	assumed	to	be	initialized	to	1	(this	allows	
for	a	mutex).
```
//	Sequential	code,	assume	that	the	input	and	output	arrays	are	created
//	outside	of	the	function
#define	MAX_VALUE	1023
function(int	input_array_size,	int	*	input_array,	int	*	output_array)
{
			int	counter;
			for(counter	=	0;	counter	<	input_array_size;	counter++)
			{
						assert(input_array[counter]	<=	MAX_VALUE);
						assert(input_array[counter]	>=	0);
						output_array[input_array[counter]]++;
			}
}
```
