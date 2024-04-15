# LC3 Writeback
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/63b994bd-ea37-4029-8133-cce3137034fb)

## LC3 Writeback Behavior
- Writes either aluout, pcout or memout based on W_Control value. This project only addresses aluout and pcout operations
- Synchronous writes to RF with dr: RegFile[dr] = DR_in
- Asynchronous reads from RF usign sr1 & sr2
- On reset, IR = 0, sr1 = 0, sr2 = 0, RF[sr1] = xxx, RF[sr2] = xxx
