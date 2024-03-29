#include <cstdint>

class LC3DecodeRefModel{
    public:
        void DecodeIR(uint16_t IR, uint8_t& W_Control, uint8_t& E_Control, uint8_t& E_Control_Valid);
};
