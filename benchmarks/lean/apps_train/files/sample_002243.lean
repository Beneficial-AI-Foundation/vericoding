The Chef has one long loaf of bread of length 1. He wants to cut it into as many little loaves as he can. But he wants to adhere to the following rule: At any moment, the length of the longest loaf which he possesses may not be larger than the length of shortest one, times some constant factor. Every time, he is only allowed to cut exactly one loaf into two shorter ones.

-----Input-----
One floating-point number, 1 ≤ k ≤ 1.999, meaning the stated constant factor. The number will have at most 3 digits after the decimal point.

-----Output-----

First, you should output one number n, the maximal achievable number of loaves for the given value of the constant factor. Then, you should output any proof that this number of loaves is in fact achievable: n-1 descriptions of cutting, using the following notation. At each step, you print two numbers: first, the index of the loaf that you want to cut into two parts; second, the length of the newly created loaf (cut off from the original one). It is assumed that the starting loaf has index 0. Each newly created loaf will be given the lowest possible free integer index (so, at the ith step this will be i). Each time, the size of size of the original loaf will be decreased by the size of the newly created loaf.

-----Example-----
Input:
1.5
Output:
4
0 0.4
0 0.3
1 0.2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded