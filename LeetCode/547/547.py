class Solution(object):
    def findCircleNum(self, isConnected):
        """
        :type isConnected: List[List[int]]
        :rtype: int
        """
        n = len(isConnected)

        cities = list(range(1,n+1,1))
        self.parent = {}
        
        for city in cities:
            self.parent[city] = city

        self.rank = dict.fromkeys(cities, 0)

        # Create unions based on matrix
        for i in range(n):
            for j in range(n):
                if isConnected[i][j] == 1:
                    self.union(i+1,j+1)

        # Traverse cities and check their union roots
        union_heads = set()

        for i in range(n):
            union_heads.add(self.find(i+1))

        # Count number of union heads
        return len(union_heads)

    def find(self, city):
        if self.parent[city] == city:
            return city
        else:
            return self.find(self.parent[city])
    
    def union(self, city_1, city_2):
        city_1_root = self.find(city_1)
        city_2_root = self.find(city_2)

        if self.rank[city_1_root] < self.rank[city_2_root]:
            self.parent[city_1_root] = city_2_root
        elif self.rank[city_1_root] > self.rank[city_2_root]:
            self.parent[city_2_root] = city_1_root
        else:
            self.parent[city_2_root] = city_1_root
            self.rank[city_1_root] += 1

provinces = Solution()
isConnected = [[1,1,0],[1,1,0],[0,0,1]]
print(provinces.findCircleNum(isConnected))