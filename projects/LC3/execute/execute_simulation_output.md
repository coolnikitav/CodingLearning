```
[GEN]:     [0]: op: rst_op | IR: 0011001010001000 | npc_in: 4c3f
[DRV]:     [5]: op: rst_op | rst: 1 | enable_execute: x | E_control: xxxxxx | IR: xxxxxxxxxxxxxxxx | VSR1: 010 | VSR2: 000 | imm5: 0000000000001000 | W_control_in: xx
[MON]:     [15]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 000 | sr2: 000 | pcout: 0000
[SCO-DRV]: [15]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 000 | sr2: 000 | pcout: 0000
[SCO-MON]: [15]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 000 | sr2: 000 | pcout: 0000
           [15]: DATA MATCH
           [15]: --------------------------------
[GEN]:     [15]: op: and_reg_op | IR: 0001111110110111 | npc_in: 7cf8
[DRV]:     [25]: op: and_reg_op | rst: 0 | enable_execute: 1 | E_control: 010001 | IR: 0101111110010111 | VSR1: 110 | VSR2: 111 | imm5: 1111111111110111 | W_control_in: 00
[MON]:     [35]: aluout: 0006 | W_control_out: 00 | dr: 111 | sr1: 110 | sr2: 111 | pcout: ff9d
[SCO-DRV]: [35]: aluout: 0006 | W_control_out: 00 | dr: 111 | sr1: 110 | sr2: 111 | pcout: ff9d
[SCO-MON]: [35]: aluout: 0006 | W_control_out: 00 | dr: 111 | sr1: 110 | sr2: 111 | pcout: ff9d
           [35]: DATA MATCH
           [35]: --------------------------------
[GEN]:     [35]: op: add_imm_op | IR: 1000111100111001 | npc_in: 62a8
[DRV]:     [45]: op: add_imm_op | rst: 0 | enable_execute: 1 | E_control: 000000 | IR: 0001111100111001 | VSR1: 100 | VSR2: 001 | imm5: 1111111111111001 | W_control_in: 00
[MON]:     [55]: aluout: fffd | W_control_out: 00 | dr: 111 | sr1: 100 | sr2: 001 | pcout: ff3d
[SCO-DRV]: [55]: aluout: fffd | W_control_out: 00 | dr: 111 | sr1: 100 | sr2: 001 | pcout: ff3d
[SCO-MON]: [55]: aluout: fffd | W_control_out: 00 | dr: 111 | sr1: 100 | sr2: 001 | pcout: ff3d
           [55]: DATA MATCH
           [55]: --------------------------------
[GEN]:     [55]: op: and_imm_op | IR: 1010001000000101 | npc_in: dc54
[DRV]:     [65]: op: and_imm_op | rst: 0 | enable_execute: 1 | E_control: 010000 | IR: 0101001000100101 | VSR1: 000 | VSR2: 101 | imm5: 0000000000000101 | W_control_in: 00
[MON]:     [75]: aluout: 0000 | W_control_out: 00 | dr: 001 | sr1: 000 | sr2: 101 | pcout: 0225
[SCO-DRV]: [75]: aluout: 0000 | W_control_out: 00 | dr: 001 | sr1: 000 | sr2: 101 | pcout: 0225
[SCO-MON]: [75]: aluout: 0000 | W_control_out: 00 | dr: 001 | sr1: 000 | sr2: 101 | pcout: 0225
           [75]: DATA MATCH
           [75]: --------------------------------
[GEN]:     [75]: op: and_reg_op | IR: 1110100010101010 | npc_in: 0e20
[DRV]:     [85]: op: and_reg_op | rst: 0 | enable_execute: 1 | E_control: 010001 | IR: 0101100010001010 | VSR1: 010 | VSR2: 010 | imm5: 0000000000001010 | W_control_in: 00
[MON]:     [95]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 008c
[SCO-DRV]: [95]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 008c
[SCO-MON]: [95]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 008c
           [95]: DATA MATCH
           [95]: --------------------------------
[GEN]:     [95]: op: lea_op | IR: 0100110010000001 | npc_in: 6c44
[DRV]:     [105]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110110010000001 | VSR1: 010 | VSR2: 001 | imm5: 0000000000000001 | W_control_in: 10
[MON]:     [115]: aluout: 0003 | W_control_out: 02 | dr: 110 | sr1: 010 | sr2: 001 | pcout: 6cc5
[SCO-DRV]: [115]:                W_control_out: 02 | dr: 110 | sr1: 010 | sr2: 001 | pcout: 6cc5
[SCO-MON]: [115]:                W_control_out: 02 | dr: 110 | sr1: 010 | sr2: 001 | pcout: 6cc5
           [115]: DATA MATCH
           [115]: --------------------------------
[GEN]:     [115]: op: add_imm_op | IR: 0000001011100100 | npc_in: 800e
[DRV]:     [125]: op: add_imm_op | rst: 0 | enable_execute: 1 | E_control: 000000 | IR: 0001001011100100 | VSR1: 011 | VSR2: 100 | imm5: 0000000000000100 | W_control_in: 00
[MON]:     [135]: aluout: 0007 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 100 | pcout: 02e7
[SCO-DRV]: [135]: aluout: 0007 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 100 | pcout: 02e7
[SCO-MON]: [135]: aluout: 0007 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 100 | pcout: 02e7
           [135]: DATA MATCH
           [135]: --------------------------------
[GEN]:     [135]: op: add_reg_op | IR: 1001111001011100 | npc_in: 5449
[DRV]:     [145]: op: add_reg_op | rst: 0 | enable_execute: 1 | E_control: 000001 | IR: 0001111001011100 | VSR1: 001 | VSR2: 100 | imm5: 1111111111111100 | W_control_in: 00
[MON]:     [155]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
[SCO-DRV]: [155]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
[SCO-MON]: [155]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
           [155]: DATA MATCH
           [155]: --------------------------------
[GEN]:     [155]: op: ne_op | IR: 0011110101011010 | npc_in: c918
[DRV]:     [165]: op: ne_op | rst: 0 | enable_execute: 0 | E_control: 000001 | IR: 0001111001011100 | VSR1: 101 | VSR2: 010 | imm5: 1111111111111010 | W_control_in: 00
[MON]:     [175]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
[SCO-DRV]: [175]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
[SCO-MON]: [175]: aluout: 0005 | W_control_out: 00 | dr: 111 | sr1: 001 | sr2: 100 | pcout: fe5d
           [175]: DATA MATCH
           [175]: --------------------------------
[GEN]:     [175]: op: add_imm_op | IR: 0111100111111000 | npc_in: 9e70
[DRV]:     [185]: op: add_imm_op | rst: 0 | enable_execute: 1 | E_control: 000000 | IR: 0001100111111000 | VSR1: 111 | VSR2: 000 | imm5: 1111111111111000 | W_control_in: 00
[MON]:     [195]: aluout: ffff | W_control_out: 00 | dr: 100 | sr1: 111 | sr2: 000 | pcout: 01ff
[SCO-DRV]: [195]: aluout: ffff | W_control_out: 00 | dr: 100 | sr1: 111 | sr2: 000 | pcout: 01ff
[SCO-MON]: [195]: aluout: ffff | W_control_out: 00 | dr: 100 | sr1: 111 | sr2: 000 | pcout: 01ff
           [195]: DATA MATCH
           [195]: --------------------------------
[GEN]:     [195]: op: lea_op | IR: 1111010100010101 | npc_in: 1a8e
[DRV]:     [205]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110010100010101 | VSR1: 100 | VSR2: 101 | imm5: 1111111111110101 | W_control_in: 10
[MON]:     [215]: aluout: fffc | W_control_out: 02 | dr: 010 | sr1: 100 | sr2: 101 | pcout: 19a3
[SCO-DRV]: [215]:                W_control_out: 02 | dr: 010 | sr1: 100 | sr2: 101 | pcout: 19a3
[SCO-MON]: [215]:                W_control_out: 02 | dr: 010 | sr1: 100 | sr2: 101 | pcout: 19a3
           [215]: DATA MATCH
           [215]: --------------------------------
[GEN]:     [215]: op: rst_op | IR: 1100011101100111 | npc_in: 905f
[DRV]:     [225]: op: rst_op | rst: 1 | enable_execute: 1 | E_control: 000110 | IR: 1110010100010101 | VSR1: 101 | VSR2: 111 | imm5: 0000000000000111 | W_control_in: 10
[MON]:     [235]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 101 | pcout: 0000
[SCO-DRV]: [235]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 101 | pcout: 0000
[SCO-MON]: [235]: aluout: 0000 | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 101 | pcout: 0000
           [235]: DATA MATCH
           [235]: --------------------------------
[GEN]:     [235]: op: add_imm_op | IR: 1000100000100010 | npc_in: 84da
[DRV]:     [245]: op: add_imm_op | rst: 0 | enable_execute: 1 | E_control: 000000 | IR: 0001100000100010 | VSR1: 000 | VSR2: 010 | imm5: 0000000000000010 | W_control_in: 00
[MON]:     [255]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 000 | sr2: 010 | pcout: 0022
[SCO-DRV]: [255]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 000 | sr2: 010 | pcout: 0022
[SCO-MON]: [255]: aluout: 0002 | W_control_out: 00 | dr: 100 | sr1: 000 | sr2: 010 | pcout: 0022
           [255]: DATA MATCH
           [255]: --------------------------------
[GEN]:     [255]: op: not_op | IR: 0011011001000010 | npc_in: 89a7
[DRV]:     [265]: op: not_op | rst: 0 | enable_execute: 1 | E_control: 100000 | IR: 1001011001000010 | VSR1: 001 | VSR2: 010 | imm5: 0000000000000010 | W_control_in: 00
[MON]:     [275]: aluout: fffe | W_control_out: 00 | dr: 011 | sr1: 001 | sr2: 010 | pcout: fe43
[SCO-DRV]: [275]: aluout: fffe | W_control_out: 00 | dr: 011 | sr1: 001 | sr2: 010 | pcout: fe43
[SCO-MON]: [275]: aluout: fffe | W_control_out: 00 | dr: 011 | sr1: 001 | sr2: 010 | pcout: fe43
           [275]: DATA MATCH
           [275]: --------------------------------
[GEN]:     [275]: op: not_op | IR: 1010000100111100 | npc_in: 501d
[DRV]:     [285]: op: not_op | rst: 0 | enable_execute: 1 | E_control: 100000 | IR: 1001000100111100 | VSR1: 100 | VSR2: 100 | imm5: 1111111111111100 | W_control_in: 00
[MON]:     [295]: aluout: fffb | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 100 | pcout: 0140
[SCO-DRV]: [295]: aluout: fffb | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 100 | pcout: 0140
[SCO-MON]: [295]: aluout: fffb | W_control_out: 00 | dr: 000 | sr1: 100 | sr2: 100 | pcout: 0140
           [295]: DATA MATCH
           [295]: --------------------------------
[GEN]:     [295]: op: add_imm_op | IR: 1100100010010010 | npc_in: 6879
[DRV]:     [305]: op: add_imm_op | rst: 0 | enable_execute: 1 | E_control: 000000 | IR: 0001100010110010 | VSR1: 010 | VSR2: 010 | imm5: 1111111111110010 | W_control_in: 00
[MON]:     [315]: aluout: fff4 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 00b4
[SCO-DRV]: [315]: aluout: fff4 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 00b4
[SCO-MON]: [315]: aluout: fff4 | W_control_out: 00 | dr: 100 | sr1: 010 | sr2: 010 | pcout: 00b4
           [315]: DATA MATCH
           [315]: --------------------------------
[GEN]:     [315]: op: lea_op | IR: 0101111011101111 | npc_in: 2144
[DRV]:     [325]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110111011101111 | VSR1: 011 | VSR2: 111 | imm5: 0000000000001111 | W_control_in: 10
[MON]:     [335]: aluout: 0011 | W_control_out: 02 | dr: 111 | sr1: 011 | sr2: 111 | pcout: 2233
[SCO-DRV]: [335]:                W_control_out: 02 | dr: 111 | sr1: 011 | sr2: 111 | pcout: 2233
[SCO-MON]: [335]:                W_control_out: 02 | dr: 111 | sr1: 011 | sr2: 111 | pcout: 2233
           [335]: DATA MATCH
           [335]: --------------------------------
[GEN]:     [335]: op: add_reg_op | IR: 0000001011101000 | npc_in: 21ee
[DRV]:     [345]: op: add_reg_op | rst: 0 | enable_execute: 1 | E_control: 000001 | IR: 0001001011001000 | VSR1: 011 | VSR2: 000 | imm5: 0000000000001000 | W_control_in: 00
[MON]:     [355]: aluout: 0003 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 000 | pcout: 02cb
[SCO-DRV]: [355]: aluout: 0003 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 000 | pcout: 02cb
[SCO-MON]: [355]: aluout: 0003 | W_control_out: 00 | dr: 001 | sr1: 011 | sr2: 000 | pcout: 02cb
           [355]: DATA MATCH
           [355]: --------------------------------
[GEN]:     [355]: op: lea_op | IR: 1111110110000111 | npc_in: 0d48
[DRV]:     [365]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110110110000111 | VSR1: 110 | VSR2: 111 | imm5: 0000000000000111 | W_control_in: 10
[MON]:     [375]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: 0ccf
[SCO-DRV]: [375]:                W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: 0ccf
[SCO-MON]: [375]:                W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: 0ccf
           [375]: DATA MATCH
           [375]: --------------------------------
[GEN]:     [375]: op: ne_op | IR: 1110000110011100 | npc_in: a0c1
[DRV]:     [385]: op: ne_op | rst: 0 | enable_execute: 0 | E_control: 000110 | IR: 1110110110000111 | VSR1: 110 | VSR2: 100 | imm5: 1111111111111100 | W_control_in: 10
[MON]:     [395]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: a048
[SCO-DRV]: [395]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: a048
[SCO-MON]: [395]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: a048
           [395]: DATA MATCH
           [395]: --------------------------------
[GEN]:     [395]: op: ne_op | IR: 1001011000011011 | npc_in: df75
[DRV]:     [405]: op: ne_op | rst: 0 | enable_execute: 0 | E_control: 000110 | IR: 1110110110000111 | VSR1: 000 | VSR2: 011 | imm5: 1111111111111011 | W_control_in: 10
[MON]:     [415]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: defc
[SCO-DRV]: [415]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: defc
[SCO-MON]: [415]: aluout: 000a | W_control_out: 02 | dr: 110 | sr1: 110 | sr2: 111 | pcout: defc
           [415]: DATA MATCH
           [415]: --------------------------------
[GEN]:     [415]: op: lea_op | IR: 1011110111101011 | npc_in: 9d0e
[DRV]:     [425]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110110111101011 | VSR1: 111 | VSR2: 011 | imm5: 0000000000001011 | W_control_in: 10
[MON]:     [435]: aluout: 000e | W_control_out: 02 | dr: 110 | sr1: 111 | sr2: 011 | pcout: 9cf9
[SCO-DRV]: [435]:                W_control_out: 02 | dr: 110 | sr1: 111 | sr2: 011 | pcout: 9cf9
[SCO-MON]: [435]:                W_control_out: 02 | dr: 110 | sr1: 111 | sr2: 011 | pcout: 9cf9
           [435]: DATA MATCH
           [435]: --------------------------------
[GEN]:     [435]: op: and_imm_op | IR: 1111010100000011 | npc_in: a679
[DRV]:     [445]: op: and_imm_op | rst: 0 | enable_execute: 1 | E_control: 010000 | IR: 0101010100100011 | VSR1: 100 | VSR2: 011 | imm5: 0000000000000011 | W_control_in: 00
[MON]:     [455]: aluout: 0000 | W_control_out: 00 | dr: 010 | sr1: 100 | sr2: 011 | pcout: fd27
[SCO-DRV]: [455]: aluout: 0000 | W_control_out: 00 | dr: 010 | sr1: 100 | sr2: 011 | pcout: fd27
[SCO-MON]: [455]: aluout: 0000 | W_control_out: 00 | dr: 010 | sr1: 100 | sr2: 011 | pcout: fd27
           [455]: DATA MATCH
           [455]: --------------------------------
[GEN]:     [455]: op: lea_op | IR: 1100101100010111 | npc_in: 7d66
[DRV]:     [465]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110101100010111 | VSR1: 100 | VSR2: 111 | imm5: 1111111111110111 | W_control_in: 10
[MON]:     [475]: aluout: fffb | W_control_out: 02 | dr: 101 | sr1: 100 | sr2: 111 | pcout: 7c7d
[SCO-DRV]: [475]:                W_control_out: 02 | dr: 101 | sr1: 100 | sr2: 111 | pcout: 7c7d
[SCO-MON]: [475]:                W_control_out: 02 | dr: 101 | sr1: 100 | sr2: 111 | pcout: 7c7d
           [475]: DATA MATCH
           [475]: --------------------------------
[GEN]:     [475]: op: lea_op | IR: 0001010011000000 | npc_in: fa5f
[DRV]:     [485]: op: lea_op | rst: 0 | enable_execute: 1 | E_control: 000110 | IR: 1110010011000000 | VSR1: 011 | VSR2: 000 | imm5: 0000000000000000 | W_control_in: 10
[MON]:     [495]: aluout: 0004 | W_control_out: 02 | dr: 010 | sr1: 011 | sr2: 000 | pcout: fb1f
[SCO-DRV]: [495]:                W_control_out: 02 | dr: 010 | sr1: 011 | sr2: 000 | pcout: fb1f
[SCO-MON]: [495]:                W_control_out: 02 | dr: 010 | sr1: 011 | sr2: 000 | pcout: fb1f
           [495]: DATA MATCH
           [495]: --------------------------------
```
