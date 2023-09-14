class Item:
    def __init__(self, profit, weight):
        self.profit = profit
        self.weight = weight

def zo_knapsack(items, capacity, current_index):
    if capacity <= 0 or current_index < 0 or current_index >= len(items):
        return 0
    elif items[current_index].weight <= capacity:
        profit1 = items[current_index].profit + zo_knapsack(items, capacity-items[current_index].weight, current_index+1)
        profit2 = zo_knapsack(items, capacity, current_index+1)
        return max(profit1, profit2)
    else:
        return 0
    
mango = Item(31, 3)
apple = Item(26, 1)
orange = Item(17, 2)
banana = Item(72, 5)

items = [mango, apple, orange, banana]

print(zo_knapsack(items, 7, 0))

