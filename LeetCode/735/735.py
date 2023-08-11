class Solution(object):
    def asteroidCollision(self, asteroids):
        """
        :type asteroids: List[int]
        :rtype: List[int]
        """
        stack = []
        for l in range(len(asteroids)):
            if not stack and asteroids[l] < 0:
                stack.append(asteroids[l])
            elif asteroids[l] < 0:
                while stack and stack[-1] > 0 and stack[-1] < -1 * asteroids[l]:
                    stack.pop()
                if not stack:
                    stack.append(asteroids[l])
                elif stack[-1] == -1 * asteroids[l]:
                    stack.pop()
                elif stack[-1] < 0:
                    stack.append(asteroids[l])
            else:
                stack.append(asteroids[l])
        return stack
