class Solution:
    def appendCharacters(self, s: str, t: str) -> int:
        t_idx = 0
        for i in range(len(s)):
            if t_idx == len(t):
                break
                
            if s[i] == t[t_idx]:
                t_idx += 1

        return len(t) - t_idx
