There is a task in Among Us in which $N$ temperature scale with unique readings are given and you have to make all of them equal. In one second you can choose an odd number and add or subtract that number in any one temperature value. Find minimum time (in seconds) required to complete the task.
$Note$: Equal value may or may not belong to array.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- First line of each testcase contains single integer $N$, the number of temperature scales
- Next line contain $A_i$ for $1 \leq i \leq N$, reading of temperature scales

-----Output:-----
For each testcase, output a single line the time (in seconds) required to complete the task.

-----Constraints-----
- $1 \leq T \leq 10^3$
- $1 \leq N \leq 10^3$
- $0 \leq A_i \leq 10^9$

-----Sample Input:-----
3

5

1 2 3 4 5

4

5 2 3 8

2

50 53  

-----Sample Output:-----
5

4

1 

-----EXPLANATION:-----
- In the $2^{nd}$ test case we need $2$ seconds to change $2$ to $8$ , $1$ second to change $3$ and $5$ to $8$ . So total time required is $2+1+1=4$ seconds.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible