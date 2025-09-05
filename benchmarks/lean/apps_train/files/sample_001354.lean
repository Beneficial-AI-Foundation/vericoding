There are $N$ sabotages available in the game Among Us, initially all at level $0$. 
$N$ imposters are allotted the task to upgrade the level of the sabotages. 
The $i^{th}$ imposter $(1 \leq i \leq N)$ increases the level of $x^{th}$ sabotage $(1 \leq x \leq N)$ by one level  if $gcd(i,x)=i$.
You need to find the number of sabotages at LEVEL 5 after all the imposters have completed their tasks.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, one integer $N$. 

-----Output:-----
For each testcase, output in a single line the number of sabotages at LEVEL 5.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq N \leq 10^{18}$

-----Sample Input:-----
1
6

-----Sample Output:-----
0

-----EXPLANATION:-----
The $1^{st}$ sabotage is at level $1$, the $2^{nd}$, $3^{rd}$ and $5^{th}$ sabotages are at level $2$, the $4^{th}$ sabotage is at level $3$ and the $6^{th}$ sabotage is at level $4$.
None of them reach level $5$. Hence the output is $0$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible