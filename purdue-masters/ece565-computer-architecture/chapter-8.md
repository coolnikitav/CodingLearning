# Main Memory

## Module 8.1 Introduction to DRAM

### Static Random Access Memory
![image](https://github.com/user-attachments/assets/f5e153a1-ac51-4a49-8d1e-2a0dde0e0e52)

### Dynamic Random Access Memory
![image](https://github.com/user-attachments/assets/d971fc32-a5d1-4c1b-a03e-419cea7a5a72)

### Brief History of DRAM
![image](https://github.com/user-attachments/assets/b0629c7e-00c7-4083-adc0-7a406a20db28)

### DRAM Basics
![image](https://github.com/user-attachments/assets/ae6104fe-72bb-425d-b429-b72ff99e662c)

Note: BLSA = bit level sense amplifiers

![image](https://github.com/user-attachments/assets/a88a615e-363b-4564-be2a-8292b1fe3036)

![image](https://github.com/user-attachments/assets/0445885b-53dd-41c5-b0d5-3c0bdf62181f)

### Optimization #1: Row buffer (page) locality for latency
- Q1: When would open page be good?
  
![image](https://github.com/user-attachments/assets/d1c4fa1c-59c8-4351-96af-382f7d9a2e1f)

-A1: Open page would be good with a lot of locality.

## Module 8.2 DRAM Bandwidth Optimizations + Error Correction

### DRAM Bandwidth
![image](https://github.com/user-attachments/assets/af101ab5-9677-4e93-9bf0-4863a4bdd91a)

### DRAM Evolution for optimization #2
![image](https://github.com/user-attachments/assets/59eeff86-9586-4caf-95d0-6e3404bf105f)

### Old 64MbitDRAM Example from Micron
![image](https://github.com/user-attachments/assets/753e80b9-ae6e-4224-b589-a7a83b89349d)

### Extended Data Out (EDO)
![image](https://github.com/user-attachments/assets/0650e413-c577-407f-a192-3ec12d0c70c8)

### Synchronous DRAM (SDRAM)
![image](https://github.com/user-attachments/assets/348dbc92-8240-46b8-9d58-8a0f9fb8ed13)

### Enhanced SDRAM & DDR
![image](https://github.com/user-attachments/assets/f63e9fb3-3acb-42e2-8ee6-f3da832bfd4a)

### Optimization #3: Interleaved Main Memory (old)
![image](https://github.com/user-attachments/assets/cb963b35-d99f-4318-853e-b9c60766099a)

### Block Interleaved Memory Systems (modern)
![image](https://github.com/user-attachments/assets/0ff20f20-1474-4045-82d4-f4b38c2c41f1)

![image](https://github.com/user-attachments/assets/19b7c9e5-6cd8-4b39-87d8-543777227d27)

### DRAM Reliability
![image](https://github.com/user-attachments/assets/28e2b840-b647-48e8-9f17-317f41a3fb47)

### DRAM Error Detection and Correction
![image](https://github.com/user-attachments/assets/0aa28cae-776f-469a-ad22-405db6da075a)

### Research: Processing in Memory
![image](https://github.com/user-attachments/assets/53f85c0c-a782-4090-8140-dc23715ca863)

## Module 8.3 Introduction to Virtual Memory

### Memory Hierarchy Review
![image](https://github.com/user-attachments/assets/bdb31dd2-b2bb-4a1b-809c-beabf81eb3fb)

### Concerete Memory Hierarchy
![image](https://github.com/user-attachments/assets/70f4195a-65b0-4ad3-bfb4-56ba191c6bcd)

### Memory Organization
![image](https://github.com/user-attachments/assets/cbbba8e2-a140-4b91-82c8-be5efc97fe47)

### Virtual Memory - basic 4 Q's
![image](https://github.com/user-attachments/assets/4307733f-5036-45d7-be00-7ce55cc67b02)

## Module 8.4 Virtual Memory Seen Through the Four-Question Framework

### Virtual Memory
![image](https://github.com/user-attachments/assets/7a22ea0c-da00-4a45-bbaf-3f9ba18217b3)

![image](https://github.com/user-attachments/assets/99f00779-4ee6-4221-8766-e4d7a3fd831d)

![image](https://github.com/user-attachments/assets/4065dde7-2fd7-49d3-8492-d229d572281a)

### Modern Uses of Virtual Memory
![image](https://github.com/user-attachments/assets/2ce0257c-3022-46cf-86ab-c1124c4b96d3)

### Virtual Memory
![image](https://github.com/user-attachments/assets/cc869fd2-d524-468a-af7d-e5a721cd5ef2)

### Back to the 4 questions
![image](https://github.com/user-attachments/assets/b3368ab2-7a55-4861-a8a4-dd7199d7c14f)

### Q2. Block Identification
![image](https://github.com/user-attachments/assets/72c4f334-ed6c-47a3-af3b-6d7efdaeec74)

### Page Table
![image](https://github.com/user-attachments/assets/226ce5e4-51f1-49fc-80c3-66294c4de320)

![image](https://github.com/user-attachments/assets/df375fd3-7abf-4f6b-9296-d1c2c5e64a44)

### Replacement
![image](https://github.com/user-attachments/assets/d3d25384-edda-4c69-a703-64c125ed36e3)

### Write Handling
![image](https://github.com/user-attachments/assets/4c4687d8-4da5-494e-8a10-6756164d4580)

### Page Table
![image](https://github.com/user-attachments/assets/a1a226ce-b30b-4829-9fbd-3ce05ed40ef1)

## Module 8.5 Introduction To TLBs

### Memory Organization Parameters
![image](https://github.com/user-attachments/assets/6af1053b-8077-458f-9081-2638f6892f6c)

### Virtual Memory
![image](https://github.com/user-attachments/assets/f437d511-4618-43e3-b4f2-f28a99f103e0)

### Exercise: Virtual Memory Design
![image](https://github.com/user-attachments/assets/9da5ab7b-a56d-48f6-849b-d20b1b8f5359)

### Address Translation
![image](https://github.com/user-attachments/assets/49f02a77-907e-41a9-82b5-379212593b07)

### Mechanics of Address Translation
![image](https://github.com/user-attachments/assets/87936ac4-3211-4ef8-909f-0cbbe4733d9c)

![image](https://github.com/user-attachments/assets/6888bd6f-970b-40d5-878f-e450554c21d9)

### Translation
![image](https://github.com/user-attachments/assets/46b9ec1f-717d-4183-9e5a-0797f25353eb)

### Translation Lookaside Buffer
![image](https://github.com/user-attachments/assets/d8d7fb96-c178-4a47-8b39-e64b7ca11fb5)

### TLB
![image](https://github.com/user-attachments/assets/63561ebf-9445-4fa5-81f6-851a3aa3f304)

### TLB + Cache
![image](https://github.com/user-attachments/assets/84ab12c2-1ef3-40ad-9f36-edd1ca2adbee)

### TLB Design
![image](https://github.com/user-attachments/assets/b127ef79-114b-4c53-b218-c6d5d85afc48)

### TLB Organization
![image](https://github.com/user-attachments/assets/17df1241-d7d5-4d96-a5af-2d9f59341468)

### Design
![image](https://github.com/user-attachments/assets/30d80e95-c296-477d-aa68-6dbbb4de51d7)

## Module 8.6 Multilevel Page Tables, Inverted Page Tables, Synonyms, Virtually Indexed, Physically Tagged Caches, Page Coloring

### TLB Performance
![image](https://github.com/user-attachments/assets/65837137-f246-4087-8ca2-0883a03ab613)

### TLB Misses and Miss Handling
![image](https://github.com/user-attachments/assets/0ddc58c5-4563-4255-a6ce-5ae5602318cf)

