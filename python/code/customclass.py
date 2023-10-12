class StarCookie:
    milk = 0.1

    def __init__(self, color, weight):
        print("The cookie is ready")
        self.color = color
        self.weight = weight

star_cookie1 = StarCookie("Red", 15)
star_cookie2 = StarCookie("Blue", 15)
star_cookie1.milk = 0.2
StarCookie.milk = 0.3
print(star_cookie1.__dict__)
print(star_cookie2.__dict__)
print(StarCookie.__dict__)
# print(star_cookie1)

# star_cookie1.weight = 15
# star_cookie1.color = "Red"
# print(star_cookie1.weight)
# print(star_cookie1.color)

# star_cookie2 = StarCookie()
# star_cookie2.weight = 16
# star_cookie2.color = "Blue"
# print(star_cookie2.weight)
# print(star_cookie2.color)

class Youtube:
    def __init__(self, username, subscribers=0, subscriptions=0):
        self.username = username
        self.subscribers = subscribers
        self.subscriptions = subscriptions

    def subscribe(self, user):
        user.subscribers += 1
        self.subscriptions += 1

user1 = Youtube("Nikita")
user2 = Youtube("Renad")
user1.subscribe(user2)
print(user1.subscribers)
print(user1.subscriptions)
print(user2.subscribers)
print(user2.subscriptions)