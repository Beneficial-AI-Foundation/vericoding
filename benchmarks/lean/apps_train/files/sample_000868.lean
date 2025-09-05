Given an array of size N$N$ and two integers K$K$ and S$S$, the special sum of a subarray is defined as follows:

(Sum of all elements of the subarray) * (K$K$ - p$p$ * S$S$)

Where p$p$ = number of distinct prime factors of “product of all elements of the subarray”.

Find the maximum special sum by considering all non-empty subarrays of the given array.

-----Input-----
- First line contains 3 integers N$N$, K$K$ and S$S$.     
- Second line contains N$N$ integers, the elements of the array.  

-----Output-----
Output a single integer. The maximum special sum considering all non-empty subarrays of the array.

-----Constraints:-----
- 1≤N,K,S≤105$ 1 \leq N, K, S \leq 10^5 $ 
- 0≤K/S≤20$ 0 \leq K / S \leq 20 $ 
- 1<$ 1 < $ Any element of array <105$ < 10^5 $

-----Sample Input-----
4 10 2

14 2 7 15

-----Sample Output-----
138

-----Sample Explanation-----
Consider the subarray {14, 2, 7}

Total number of distinct prime factors in it is 2 (2 and 7).

Therefore, value of special sum is (14 + 2 + 7) * (10 - 2 * 2) = 138.

This is the subarray with the maximum special sum.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
