Nexus 4.O is going to be organized by ASME, GLA University. Shubhanshu, Head of Finance Team is working for it. He has $N$ number of bills of different values as $a$$1$,$ a$$2$, $a$$3$…$a$$n$.
He is interested in a game in which one has to do the addition of the bills. But due to privacy concerns, he cannot share the details with others. 
He can only trust his best friend Avani with such a confidential thing. So, he asked her to play this game.
Rules of the game :
- Avani needs to answer $Q$ queries.
- Every $Q$$i$ query has 2 values $X$$i$ and $Y$$i$.
- Avani needs to find the sum of the values between $X$$i$ and $Y$$i$ (inclusive).
So, you need to help Avani in answering the $Q$ queries

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- The first line of each test case contains the value $N$ and $Q$.
- The second line of each test case contains the $N$ space-separated values as $a$$1$,$ a$$2$, $a$$3$…$a$$n$.
- The next line of each test case containing $Q$ query with $X$$i$ and $Y$$i$.

-----Output:-----
For each test case, Print the total amount between $X$$i$ and $Y$$i$ for $Q$ number of queries.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 10^5$
- $1 \leq Q \leq 10^5$
- $1 \leq a$$i$$ \leq 10^9$

-----Subtasks (25 points) :-----
- $1 \leq N \leq 10^2$.
- $1 \leq Q \leq 10^2$.
- $1 \leq a$$i$$ \leq 10^5$.

-----Subtasks (25 points) :-----
- $1 \leq N \leq 10^3$.
- $1 \leq Q \leq 10^3$.
- $1 \leq a$$i$$ \leq 10^5$.

-----Subtasks (50 points) :-----
- $Original  Constraints$.

-----Sample Input:-----
1
8 3
1 2 3 4 5 6 7 8
2 3
1 6
5 8

-----Sample Output:-----
5
21
26

-----EXPLANATION:-----
$Q$$1$ : (2,3) 2+3=5
$Q$$2$ : (1,6) 1+2+3+4+5+6=21
$Q$$3$ : (5,8) 5+6+7+8=26

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded