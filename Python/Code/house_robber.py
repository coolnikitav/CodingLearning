def house_robber(houses, current_index):
  if current_index >= len(houses):
    return 0
  else:
    steal_first_house = houses[current_index] + house_robber(houses, current_index + 2)
    skip_first_house = house_robber(houses, current_index + 1)
    return max(steal_first_house, skip_first_house)

houses = [6,7,1,30,8,2,4]
print(house_robber(houses, 0))
