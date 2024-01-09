def minNumberOfHours(initialEnergy, initialExperience, energy, experience):
        """
        :type initialEnergy: int
        :type initialExperience: int
        :type energy: List[int]
        :type experience: List[int]
        :rtype: int
        """
        xp_gap = 0
        xp_bonus = 0
        energy_bonus = 1

        for energy,xp in zip(energy, experience):
            initialEnergy -= energy
            if initialExperience-xp <= xp_gap:
                xp_gap = initialExperience-xp
                xp_bonus = 1
            initialExperience += xp

        if initialEnergy > 0:
            initialEnergy = 0
            energy_bonus = 0

        hours = -(initialEnergy-energy_bonus) - (xp_gap-xp_bonus)
        return hours if hours > 0 else 0

print(minNumberOfHours(30, 78, [24,91,63,38,31,63,22,35,91,54,88,46,80,14,12,19,57,92], [18,43,36,88,84,21,82,54,61,80,68,54,75,27,99,14,86,95]))
print(minNumberOfHours(5, 3, [1,4,3,2], [2,6,3,1]))
print(minNumberOfHours(5, 3, [1,4], [2,5]))
print(minNumberOfHours(3, 2, [1], [2]))
