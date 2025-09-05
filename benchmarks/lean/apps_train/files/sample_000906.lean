There are two friends Alice and Bob. They have a packet of $n$ candies. They want to split the candies between them, and to do so, they kept them all in a single line. The $i^{\text{th}}$ candy in the line has a sweetness value of $a_i$. They decided to take turns in picking the candies. Alice has the first turn. In a person's turn, they either eat the leftmost candy or the rightmost candy with equal probability.
Can you find the expected value of sum of sweetness of the candies eaten by Alice?
Your answer is considered correct if its absolute or relative error doesn't exceed $10^{-6}$ .

-----Input:-----
- The first line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains a single integer $n$ denoting the number of candies.
- Second line of each testcase contains  $n$ space separated integers representing $a_1,a_2,a_3,...a_n$ respectively.

-----Output:-----
For each testcase, output the expected value of sum of sweetness of the candies which Alice eats.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq n \leq 10^3$
- $1 \leq a_i \leq 10^6$
- Sum of $n$ across all the tests $\leq 10^3$

-----Sample Input:-----
2
2
1 2
3
1 2 3

-----Sample Output:-----
1.500000000000000
4.000000000000000

-----EXPLANATION:-----
In the first sample, Alice eats either the first or the second candy with equal probability. Hence, expected value is $(1+2)/2 = 1.5$
For the second sample, expected value is $4$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded