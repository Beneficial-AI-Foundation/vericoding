Given an empty array A of infinite length and a positive integer K you have to process 
Q queries of type:    
- ! l r x: Fill the value x in all the empty places in the array from index l to r  (both inclusive).
- ? l r: Print the number of prime factors of K which is also a prime factor of at least one number in A[l], A[l + 1], A[l + 2], … A[r].   

-----Input-----
- The first line contains two space separated integers K and Q respectively.
- Then Q lines follow:
- Each of the $i^{th}$ line contains one of the above two types of queries.

-----Output-----
For each query of the second type, print in a new line the answer to that query. i.e. number of prime factors of K which is also a prime factor of at least one number in A[l], A[l + 1], A[l + 2], … A[r].   

-----Constraints-----
- $1 \leq K, x \leq 10^9$
- $ 1 \leq l \leq r \leq 10^5$
- $ 1 \leq Q \leq 10^5$ 

-----Sample Input-----
20 5

? 1 5

! 3 5 4

? 1 5

! 1 4 15

? 1 5   

-----Sample Output-----
0

1

2   

-----EXPLANATION-----
Initially, all the places in the array are empty. i.e _ _ _ _ _

After first update the array looks like: _ _ 4 4 4

In the range [1, 5] the only factor of 20 which is also a prime factor of at least one number in _ _ 4 4 4  is 2.

After the second update the array looks like: 15 15 4 4 4

In the range [1, 5] the prime factors of 20 i.e. 5 is a prime factor of 15, 15 and 2 is the prime factor of 4, 4, 4.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded