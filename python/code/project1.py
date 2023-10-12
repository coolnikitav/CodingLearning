numDays = input("How many day's temperature? ")
temp = []
for i in range(int(numDays)):
    dayTemp = input(f"Day {i+1} temperature is ")
    temp.append(int(dayTemp))
avgTemp = round(sum(temp)/len(temp),2)
print(f"Average is: {avgTemp}")
highTemp = [num for num in temp if num > avgTemp]
print(f"Number of days above average: {len(highTemp)}")