As engineers put more transistors on a chip, companies are increasing the number of cores on each chip.
What other feasible choices could they have made instead?
- Increase the size of cache on chip -> increase hit rate -> increase speed at which we operate on instructions. But we dont do that because we dont get as much of an improvement.

Why do ISRs have priorities associated with them whereas normal procedures do not?
- Procedures are called and executed in the order dictated by program flow. ISRs have situations where it is not necessary to do a certain ISR if a higher priority one is in play (arithmetic overflow getting overshadowed by user hardware IO interrupt).
 
