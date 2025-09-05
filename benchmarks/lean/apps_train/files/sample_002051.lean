Arkady plays Gardenscapes a lot. Arkady wants to build two new fountains. There are n available fountains, for each fountain its beauty and cost are known. There are two types of money in the game: coins and diamonds, so each fountain cost can be either in coins or diamonds. No money changes between the types are allowed.

Help Arkady to find two fountains with maximum total beauty so that he can buy both at the same time.

-----Input-----

The first line contains three integers n, c and d (2 ≤ n ≤ 100 000, 0 ≤ c, d ≤ 100 000) — the number of fountains, the number of coins and diamonds Arkady has.

The next n lines describe fountains. Each of these lines contain two integers b_{i} and p_{i} (1 ≤ b_{i}, p_{i} ≤ 100 000) — the beauty and the cost of the i-th fountain, and then a letter "C" or "D", describing in which type of money is the cost of fountain i: in coins or in diamonds, respectively.

-----Output-----

Print the maximum total beauty of exactly two fountains Arkady can build. If he can't build two fountains, print 0.

-----Examples-----
Input
3 7 6
10 8 C
4 3 C
5 6 D

Output
9

Input
2 4 5
2 5 C
2 1 D

Output
0

Input
3 10 10
5 5 C
5 5 C
10 11 D

Output
10

-----Note-----

In the first example Arkady should build the second fountain with beauty 4, which costs 3 coins. The first fountain he can't build because he don't have enough coins. Also Arkady should build the third fountain with beauty 5 which costs 6 diamonds. Thus the total beauty of built fountains is 9.

In the second example there are two fountains, but Arkady can't build both of them, because he needs 5 coins for the first fountain, and Arkady has only 4 coins.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded