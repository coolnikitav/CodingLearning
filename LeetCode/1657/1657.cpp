class Solution(object):
    def closeStrings(self, word1, word2):
        """
        :type word1: str
        :type word2: str
        :rtype: bool
        """
        
        if len(word1) != len(word2):
            return False
        
        # Create a dictionary from each word
        letters1 = Counter(word1)
        letters2 = Counter(word2)

        # Check if words have the same letters
        # Sets do not allow duplicates, so each letter is unique in each set
        if set(letters1.keys()) != set(letters2.keys()):
            return False
        
        # Check if occurences are identical
        if sorted(letters1.values()) != sorted(letters2.values()):
            return False

        return True
