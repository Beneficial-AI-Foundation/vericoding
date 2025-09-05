Kabir Singh is playing a game on the non-negative side of  x-axis. It takes him $1 second$ to reach from Pth position to (P−1)th position or (P+1)th position. 
Kabir never goes to the negative side and also doesn't stop at any moment of time.
The movement can be defined as  : 
- At the beginning he is at $x=0$ , at time $0$
- During the first round, he moves towards $x=1$ and comes back to the $x=0$ position.
- In the second round, he moves towards the $x=2$ and comes back again to $x=0$.
- So , at $Kth$ round , he moves to $x=K$ and comes back to $x=0$
So in this way game goes ahead.
For Example, the path of Kabir for $3rd$ round is given below.
$0−1−2−3−2−1−0$
The overall path followed by Kabir would look somewhat like this:
$0−1−0−1−2−1−0−1−2−3−2−1−0−1−2−3−4−3−…$
Now the task is , You are given Two Non-Negative integers $N$ , $K$ .
You have to tell the time at which Kabir arrives at $x=N$ for the $Kth$ time.
Note - Kabir visits all the points , he can not skip or jump over one point.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, two integers $N, K$. 

-----Output:-----
For each testcase, output in a single line answer i.e Time Taken by Kabir Singh modulo 1000000007.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $0 \leq N \leq 10^9$
- $1 \leq K \leq 10^9$

-----Sample Input:-----
4

0 1
1 1
1 3
4 6

-----Sample Output:-----
0
1
5
46

-----EXPLANATION:-----
Test Case 1:
Kabir starts the journey from the $N=0$ at time $t=0$ and it's the first time$ (K=1)$, he is here. So, the answer is $0$.
Test Case 3:
The path followed by Kabir to reach 1 for the third time is given below.
$0−1−0−1−2−1$
He reaches $1$ for the third time at $ t=5$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
