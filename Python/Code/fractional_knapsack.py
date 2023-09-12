class Item:
    def __init__(self, weight, value):
        self.weight = weight
        self.value = value
        self.ratio = value / weight

def knapsack_method(items, capacity):
    items.sort(key=lambda x: x.ratio, reverse = True)
    used_capacity = 0
    total_value = 0
    for item in items:
        if used_capacity + item.weight <= capacity:
            used_capacity += item.weight
            total_value += item.value
        else:
            unused_weight = capacity - used_capacity
            value = item.ratio * unused_weight
            used_capacity += unused_weight
            total_value += value

        if used_capacity == capacity:
            break

    print("Total value obtained: " + str(total_value))

item1 = Item(20, 100)
item2 = Item(30, 120)
item3 = Item(10, 60)
c_list = [item1, item2, item3]

knapsack_method(c_list, 50)