# Small Multiprocessors

## Bus Implementation

### Symmetric Multiprocessors
- Q: What is meant by symmetric in this context?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eed4ba30-8cd2-416d-9510-3c532182c4d5)

### Multidrop Memory Bus
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ca43fe9-e242-4a7d-be61-456f8fbe50de)

### Pipelined Memory Bus
- Q: What is the advantage of the pipelined bus?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ca43fe9-e242-4a7d-be61-456f8fbe50de)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/21a286d9-8b89-4748-a37b-ee9e94f5e8ca)

- A: Instead of getting the control of the whole bus, access is pipelined and use only when needed.

## Cache Coherence

### Memory Coherence in SMPs
- Q: What happens in CPU-1 updates A to 200 in case of write-back and write-through.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e4d7f00d-70f9-4fe6-9a25-39599f27223e)

Stale values matter because the other CPU will not see the new value. There is no communication.

### Write-back Caches & SC
This is write-back cache:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/071db50b-b3e1-47a4-a732-5117d1157958)

Even SC consistent code can end up with inconsistent values when we introduce caches.

### Write-through Caches & SC
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/68ba87b5-fc8d-42c3-93b6-7354d7d29f56)

### Cache Coherence vs Memory Consistency
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f16b165-19cf-49f5-b68f-95e5e8ad526f)
