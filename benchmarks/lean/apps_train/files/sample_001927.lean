A permutation p of size n is the sequence p_1, p_2, ..., p_{n}, consisting of n distinct integers, each of them is from 1 to n (1 ≤ p_{i} ≤ n).

A lucky permutation is such permutation p, that any integer i (1 ≤ i ≤ n) meets this condition p_{p}_{i} = n - i + 1.

You have integer n. Find some lucky permutation p of size n.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 10^5) — the required permutation size.

-----Output-----

Print "-1" (without the quotes) if the lucky permutation p of size n doesn't exist.

Otherwise, print n distinct integers p_1, p_2, ..., p_{n} (1 ≤ p_{i} ≤ n) after a space — the required permutation.

If there are multiple answers, you can print any of them.

-----Examples-----
Input
1

Output
1 

Input
2

Output
-1

Input
4

Output
2 4 1 3 

Input
5

Output
2 5 3 1 4

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded