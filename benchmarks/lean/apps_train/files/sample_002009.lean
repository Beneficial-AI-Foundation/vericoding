Permutation p is an ordered set of integers p_1,   p_2,   ...,   p_{n}, consisting of n distinct positive integers not larger than n. We'll denote as n the length of permutation p_1,   p_2,   ...,   p_{n}.

Your task is to find such permutation p of length n, that the group of numbers |p_1 - p_2|, |p_2 - p_3|, ..., |p_{n} - 1 - p_{n}| has exactly k distinct elements.

-----Input-----

The single line of the input contains two space-separated positive integers n, k (1 ≤ k < n ≤ 10^5).

-----Output-----

Print n integers forming the permutation. If there are multiple answers, print any of them.

-----Examples-----
Input
3 2

Output
1 3 2

Input
3 1

Output
1 2 3

Input
5 2

Output
1 3 2 4 5

-----Note-----

By |x| we denote the absolute value of number x.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded