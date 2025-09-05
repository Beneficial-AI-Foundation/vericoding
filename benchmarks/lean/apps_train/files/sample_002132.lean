A new pack of n t-shirts came to a shop. Each of the t-shirts is characterized by three integers p_{i}, a_{i} and b_{i}, where p_{i} is the price of the i-th t-shirt, a_{i} is front color of the i-th t-shirt and b_{i} is back color of the i-th t-shirt. All values p_{i} are distinct, and values a_{i} and b_{i} are integers from 1 to 3.

m buyers will come to the shop. Each of them wants to buy exactly one t-shirt. For the j-th buyer we know his favorite color c_{j}.

A buyer agrees to buy a t-shirt, if at least one side (front or back) is painted in his favorite color. Among all t-shirts that have colors acceptable to this buyer he will choose the cheapest one. If there are no such t-shirts, the buyer won't buy anything. Assume that the buyers come one by one, and each buyer is served only after the previous one is served.

You are to compute the prices each buyer will pay for t-shirts.

-----Input-----

The first line contains single integer n (1 ≤ n ≤ 200 000) — the number of t-shirts.

The following line contains sequence of integers p_1, p_2, ..., p_{n} (1 ≤ p_{i} ≤ 1 000 000 000), where p_{i} equals to the price of the i-th t-shirt.

The following line contains sequence of integers a_1, a_2, ..., a_{n} (1 ≤ a_{i} ≤ 3), where a_{i} equals to the front color of the i-th t-shirt.

The following line contains sequence of integers b_1, b_2, ..., b_{n} (1 ≤ b_{i} ≤ 3), where b_{i} equals to the back color of the i-th t-shirt.

The next line contains single integer m (1 ≤ m ≤ 200 000) — the number of buyers. 

The following line contains sequence c_1, c_2, ..., c_{m} (1 ≤ c_{j} ≤ 3), where c_{j} equals to the favorite color of the j-th buyer. The buyers will come to the shop in the order they are given in the input. Each buyer is served only after the previous one is served.

-----Output-----

Print to the first line m integers — the j-th integer should be equal to the price of the t-shirt which the j-th buyer will buy. If the j-th buyer won't buy anything, print -1.

-----Examples-----
Input
5
300 200 400 500 911
1 2 1 2 3
2 1 3 2 1
6
2 3 1 2 1 1

Output
200 400 300 500 911 -1 

Input
2
1000000000 1
1 1
1 2
2
2 1

Output
1 1000000000

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded