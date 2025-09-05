On fictional islands of Matunga archipelage several different tribes use fictional currency - tung. One tung is a very small amount, so all payments are made with coins of different values. For example, one tribe use coins of 7 and 9 tungs, another - 6, 10 and 11 tungs. Every tribe has at least 2 different coins.
Also every tribe has a shop with remarkable feature: if you find an item N tungs worth, you always can find an item priced N+1 tungs in the same shop.
Your goal is to write the function min_price(coins) which finds out the minimum price of item which can be in sale in Matunga tribe shop, knowing the values of coins used there.

Function should return -1 if result is not accessible (i.e. coins of these values can't cover natural row from N to infinity without gaps).

For example, some tribe has coins of 3 and 5 tungs. They can't sell items of 4 or 7 tungs, because 4 and 7 can't be represented as a sum of 3's and 5's. But starting from 8 tungs you can do it with every sum: 8 is 5+3, 9 is 3+3+3, 10 is 5+5, 11 is 5+3+3 and so on. So the answer for this set of coins is 8.

def min_price (coins : List Int) : Int := sorry

def min_int (a b : Int) : Int := if a ≤ b then a else b

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
