![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3b146a53-155e-49a7-b8ae-54355573a89d)# Designing finite state machines

## Mealy vs Moore machine
Mealy machine depends on inputs and the present state.

Moore machine only depends on the present state.

## Mealy - 101 Non-overlapping sequence detector

When 101 is found, output will be 1. If its 10101, machine will not give the output twice.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f8a3bd76-1c65-4837-ad27-70bb3bbc470f)

## Mealy - 011 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c1538ac8-9570-4ac3-9fa6-3ea6b5f9fec7)

## Mealy - 000 non-overlapping sequence detector 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/83c255d7-8ea2-49ca-968f-ef1f7c6665f9)

## Mealy - 0101 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e3d3bd3e-0695-454d-95cd-794c4588f8dc)

## Mealy - 11011 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0a08ae42-2916-44d9-a0ff-13e4506bdc34)

## Mealy - 101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ceb3992d-a847-4f99-ae3d-4a3dc91f43ee)

## Mealy - 011 Overlapping sequence detector
Will behave the same way as non-overlapping because 011011, there are no bits that could overlap.
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/75280ae0-eacf-43e9-94a2-b456500015ac)

## Mealy - 000 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4e68db09-78f4-4fba-bf2f-31fafbeab3e3)

## Mealy - 0101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/05ba8c09-8b08-4035-9de6-e01004331d7d)

## Mealy - 11011 Overlapping Sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ea42afdf-dcb5-4848-902d-84179499e7e1)

## Designing a mealy machine - Sequence detector
We will write code for 001. It is the same for overlapping and non-overlapping.

We will use binary encoding logic instead of one-hot.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dc93119f-7a3f-43f8-85df-5f33dc932210)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe2d0edd-18ef-482c-9a11-e1074475a243)

```
module seq_001(det,inp,clk,reset);
  input inp,clk,reset;
  output reg det;

  parameter s0=2'b00, s1=2'b01, s2=2'b10;
  reg [1:0] pr_state, nxt_state;

  always@(posedge clk)
    if(reset)
      pr_state <= s0;
    else
      pr_state <= nxt_state;

  always@(inp, pr_state)
    case(pr_state)
      s0:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s1;
      s1:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s2;
      s2:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s2;
      default: nxt_state = s0;
    endcase

  always@(inp,pr_state)
    case (pr_state)
      s0: det = 0;
      s1: det = 0;
      s2:
        if(inp)
          det = 1;
        else
          det = 0;
        default: det = 0;
    endcase
endmodule
```

## Moore - 101 Non-overlapping sequence detector

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d2a1a3b1-e83f-497a-9f05-6e9f5415e5fc)

## Moore - 010 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eeba8910-b7ea-4798-bb64-4b9fc77e5e12)

## Moore - 0101 Non-overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3bfbf35f-d5aa-4646-b06f-37320078789d)

## Moore - 101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1deffe0b-80c8-4e81-8225-b34ea101fd53)

## Moore - 010 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/65d6b91e-eec2-4ce7-99bd-94d5879a47ae)

## Moore - 0101 Overlapping sequence detector
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ec6b77d0-0a99-44fb-bcef-d3640b79635c)

## Designing a Moore machine - Sequence detector
Same 001 sequence detector:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7104d062-1407-4418-a23c-0f224c40d0f3)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/44dc5ab2-478a-467b-a1f9-6ccb37179e81)
```
module seq_moore_001(det,inp,clk,reset);
  input clk,reset,inp;
  output reg det;

  parameter s0=2'b00,s1=2'b01,s2=2'b10,s3=2'b11;
  reg [1:0] pr_state,nxt_state;

  always@(posedge clk)
    if(reset)
      pr_state <= s0;
    else
      pr_state <= nxt_state;

  always@(inp,pr_state)
    case(pr_state)
      s0:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s1;
      s1:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s2;
      s2:
        if(inp)
          nxt_state = s3;
        else
          nxt_state = s2;
      s3:
        if(inp)
          nxt_state = s0;
        else
          nxt_state = s1;
      default: nxt_state = s0;
    endcase

  always@(pr_state)
    case(pr_state)
      s0: det = 0;
      s1: det = 0;
      s2: det = 0;
      s3: det = 1;
      default: det = 0;
    endcase

endmodule
```
