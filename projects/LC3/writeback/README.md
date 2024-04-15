# LC3 Writeback
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9249223f-aa46-4c46-b533-e8c089403ab3)

## LC3 Writeback Behavior
- Writes either aluout, pcout or memout based on W_Control value. This project only addresses aluout and pcout operations
- Synchronous writes to RF with dr: RegFile[dr] = DR_in
- Asynchronous reads from RF usign sr1 & sr2
- On reset, IR = 0, sr1 = 0, sr2 = 0, RF[sr1] = xxx, RF[sr2] = xxx

## RegFile
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/571263a9-298d-4e3d-8583-f816980c0bf8)

## LC3 Writeback Internals
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d7c9fe6a-575b-4bf6-a625-5b9a02ed9dc1)
