We all know Gru loves Agnes very much. One day Agnes asked Gru to answer some of her queries. She lined up $N$ minions in a straight line from $1$ to $N$. 
You are given an array $A$ which contains the height of minions. Agnes will ask him several queries. In each query, Gru has to tell whether the bitwise AND of  $A[L \ldots R]$ is EVEN or ODD. Since Gru is busy planning the biggest heist on Earth, he asks for your help.

-----Input:-----
- First line of the input contains an integer $T$ denoting the number of test cases.
For each test case:-
- First line contains an integer $N$ denoting the number of elements.
- Second line contains $N$ spaced integer representing array elements.
- Third line contains $Q$ representing number of query.
- Next $Q$ lines contains two integer $L$ and $R$ as defined above.

-----Output:-----
For each query, output "EVEN" or "ODD" without quotes.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $1 \leq A_i \leq 10^5$
- $1 \leq Q \leq 10^5$

-----Sample Input:-----
1
5
1 3 2 4 5
3
1 2 
1 5
3 4

-----Sample Output:-----
ODD
EVEN
EVEN

-----Explanation-----
- For the first query, the bitwise AND of 1 and 3 is 1, which is Odd. Hence the first output is ODD.
- For the third query, the bitwise AND of 2 and 4 is 0, which is Even. Hence the third output is EVEN.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded