Nobody knows, but $N$ frogs live in Chef's garden.
Now they are siting on the X-axis and want to speak to each other. One frog can send a message to another one if the distance between them is less or equal to $K$.
Chef knows all $P$ pairs of frogs, which want to send messages. Help him to define can they or not!
Note : More than $1$ frog can be on the same point on the X-axis.

-----Input-----
- The first line contains three integers $N$, $K$ and $P$.
- The second line contains $N$ space-separated integers $A_1$, $A_2$, …, $A_N$ denoting the x-coordinates of frogs".
- Each of the next $P$ lines contains two integers $A$ and $B$ denoting the numbers of frogs according to the input.

-----Output-----
For each pair print "Yes" without a brackets if frogs can speak and "No" if they cannot.

-----Constraints-----
- $1 \le N, P \le 10^5$
- $0 \le A_i, K \le 10^9$
- $1 \le A, B \le N$

-----Example-----

-----Sample Input:-----
5 3 3
0 3 8 5 12
1 2
1 3
2 5

-----Sample Output:-----
Yes
Yes
No

-----Explanation-----
- 
For pair $(1, 2)$ frog $1$ can directly speak to the frog $2$ as the distance between them is $3 - 0 = 3 \le K$ . 
- 
For pair $(1, 3)$ frog $1$ can send a message to frog $2$, frog $2$ can send it to frog $4$ and it can send it to frog $3$.
- 
For pair $(2, 5)$ frogs can't send a message under current constraints.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded