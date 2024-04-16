# LC3 Writeback
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/42af1a34-6314-4213-843d-64c6270d85e4)

## LC3 Writeback Behavior
- Writes either aluout, pcout or memout based on W_Control value. This project only addresses aluout and pcout operations
- Synchronous writes to RF with dr: RegFile[dr] = DR_in
- Asynchronous reads from RF usign sr1 & sr2

## RegFile
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/571263a9-298d-4e3d-8583-f816980c0bf8)

## LC3 Writeback Internals
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d7c9fe6a-575b-4bf6-a625-5b9a02ed9dc1)
