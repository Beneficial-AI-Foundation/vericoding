There are $N$ robots who work for $Y$ days and on each day they
produce some toys .on some days a few robots are given rest.
So depending on the availability of robots owner has 
made a time table which decides which robots will work on 
the particular day.
Only contiguous robots must be selected as they can form 
a link of communication among themselves.
Initially, all robots have the capacity of one toy.
On each day capacity for the chosen robot is updated i.e
capacity = capacity $+$$ ($minimum capacity of given range % $1000000007)$ .
After calculating the minimum capacity of a given range, compute
it as modulo 1000000007 ($10^9 + 7$).
After $Y$ days find the minimum capacity of the $N$ robots and compute it as modulo 1000000007 ($10^9 + 7$).   

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Next Line contains a single integer N.
- Next Line contains a single integer Y.
- Next $Y$ lines contains l and r range of chosen robots .

-----Output:-----
For each testcase, output in a single line answer , the minimum capacity of the $N$ robots after $Y$ days and compute it as modulo 1000000007 ($10^9 + 7$) .

-----Constraints-----
- $1 \leq T \leq 100$
- $100 \leq N \leq 10^4$
- $200 \leq Y \leq 1000$
- $0<=l , r<=N-1$  , $l<=r$

-----Sample Input:-----
1
5
4
0 3
1 2
4 4
0 4

-----Sample Output:-----
4

-----EXPLANATION:-----
Initial capacity of the $5$ robots
1 1 1 1 1 
Minimum in range [0,3] = 1
Update the capacity in the range [0,3]
Now capacity becomes, 
Day 1 - 2 2 2 2 1
Similarly capacities changes for each day 
Day 2 - 2 4 4 2 1
Day 3 - 2 4 4 2 2
Day 4 - 4 6 6 4 4
so after 4 days minimum capacity is $4$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
