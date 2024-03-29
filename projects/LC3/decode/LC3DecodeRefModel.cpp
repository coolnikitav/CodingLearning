#include "LC3DecodeRefModel.h"

void LC3DecodeRefModel::DecodeIR(uint16_t IR, uint8_t& W_Control, uint8_t& E_Control, uint8_t& E_Control_Valid) {
    uint8_t opcode = (IR >> 12) & 0xF;  // IR[15:12]
    uint8_t IR5    = (IR >> 5)  & 0b1;  // IR[5]

    W_Control       = 0;
    E_Control       = 0;
    E_Control_Valid = 0xFF;  // All bits valid by default. This handles don't care bits

    switch (opcode) {
        case 0b0001:  // ADD
            W_Control       = 0b00;
            if (IR5 == 0b0) {
                E_Control   = 0b000001;
            } else {
                E_Control   = 0b000000;
            }
            E_Control_Valid = 0b110001;
            break;
        case 0b0101:  // AND
            W_Control       = 0b00;
            if (IR5 == 0b0) {
                E_Control   = 0b010001;
            } else {
                E_Control   = 0b010000;
            }
            E_Control_Valid = 0b110001;
            break;
        case 0b1001:  // NOT
            W_Control       = 0b00;
            E_Control       = 0b100000;
            E_Control_Valid = 0b110000;
            break;
        case 0b1110:// LEA
            W_Control       = 0b10;
            E_Control       = 0b000110;
            E_Control_Valid = 0b001110;
            break;
    }
}
