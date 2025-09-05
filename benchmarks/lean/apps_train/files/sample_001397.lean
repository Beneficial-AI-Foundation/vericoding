Kshitij has recently started solving problems on codechef. As he is real problem solving enthusiast, he wants continuous growth in number of problems solved per day.
He started with $a$  problems on first day. 
He solves $d$ problems more than previous day. But after every $k$ days , he increases $d$ by
$inc$ .
Can you guess how many questions he will solve on $nth $ day ?

-----Input:-----
- First line  contains $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input,five integers $a, d, k, n, inc$. 

-----Output:-----
For each testcase, output in a single line number of questions solved on $nth$ day.

-----Constraints-----
- $1 \leq T \leq 15$
- $1 \leq a \leq 99$
- $1 \leq d \leq 100$
- $1 \leq n \leq 10000$
- $1 \leq k \leq n$
- $0 \leq inc \leq 99$

-----Sample Input:-----
1
1 4 3 8 2

-----Sample Output:-----
43

-----EXPLANATION:-----
The number of questions solved in first 8 days is :
$1$ $5$ $9$ $15$ $21$ $27$ $35$ $43$ .
On first day he solved 1 problem . Here $d$ is  4 for first 3 days.
Then after 3 days $d$ increases by 2 (that is 6).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible