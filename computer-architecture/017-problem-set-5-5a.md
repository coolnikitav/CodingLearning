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
