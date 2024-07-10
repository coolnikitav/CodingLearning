As engineers put more transistors on a chip, companies are increasing the number of cores on each chip.
What other feasible choices could they have made instead?
- Increase the size of cache on chip -> increase hit rate -> increase speed at which we operate on instructions. But we dont do that because we dont get as much of an improvement.

--------------------------------------------------------------------

Why do ISRs have priorities associated with them whereas normal procedures do not?
- Procedures are called and executed in the order dictated by program flow. ISRs have situations where it is not necessary to do a certain ISR if a higher priority one is in play (arithmetic overflow getting overshadowed by user hardware IO interrupt).

 --------------------------------------------------------------------
 
Why do IO devices place the interrupt vector on the bus?
- To signal that an interrupt needs to be processed
 ![image](https://github.com/coolnikitav/learning/assets/30304422/80b1f414-1f82-424d-abae-eb4312815493)

--------------------------------------------------------------------

![image](https://github.com/coolnikitav/learning/assets/30304422/833ebeb7-9ac1-407b-88ec-00e96137d2cc)
- Mean access time = 1 + 0.75*100 = 76ms

--------------------------------------------------------------------
![image](https://github.com/coolnikitav/learning/assets/30304422/46301697-d872-4916-9b6a-f8df2a071f7f)
- direct-mapped cache = 1-way set associative
- Cache A can hold 2^15B of memory or 32KB

![image](https://github.com/coolnikitav/learning/assets/30304422/9bd4d95e-79f9-43f3-b88f-ac9747c39129)
- Cache B can hold 2^5*2^3*2^7 = 2^15B or 32KB

Which cache is likely to have a higher hit rate? Why?
- Caches are the same size. So 8-way will have a higher hit rate due to higher associativity.

Which cahce is likely to have a shorter access time? Why?
- Direct-mapped because we only need to look at one line instead of multiple lines in a set.

--------------------------------------------------------------------

![image](https://github.com/coolnikitav/learning/assets/30304422/76617c4a-12e0-42ae-b35a-4f2609a89c12)
- Cache A can hold 32K-Words or 64KB
- Cache B can hold 64KB

--------------------------------------------------------------------

![image](https://github.com/coolnikitav/learning/assets/30304422/6d8fea2c-fb17-4b52-8b34-fd7db2523a9a)

- Speedup = 1/(0.75 + 0.25/2) = 1/0.875 = 8/7

--------------------------------------------------------------------
