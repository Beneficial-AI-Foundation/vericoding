Note : This question carries $150$ $points$
There is an outcry in Middle Earth, as the greatest war between Orgs of Dark Lord Sauron and Frodo Baggins is about to begin. To end the war, Frodo decides to destroy the ring in the volcano of Mordor. There are many ships that lead Frodo to Mordor, and he is confused about which one he should board.  Given two-ship numbers $M$ and $N$, Frodo has to solve a problem to find the ship which he should board.
Find the number of pairs (x, y), such that $1<=x<=M$ and $1<=y<=N$, for which $x*y + x+ y = string(x)+string(y)$ is true. 
Also, calculate the number of distinct x satisfying the given condition.  The number of pairs and the number of distinct x will help select Frodo the boat he should board. Help Frodo defeat Sauron. 

-----Input :-----
- First line contains $T$ as number of test cases 
- Each test case contains two integers $M$ and $N$ 

-----Output :-----
- For each test case, print two integers - the number of such pairs (x,y) and the number of distinct x

-----Constraints :-----
- 1 ≤ T ≤ 5000
- 1 ≤  M, N ≤ 10^9

-----Sample Input :-----
1
1 9

-----Sample Output :-----
1 1

-----Explanation :-----
For test case two M=1 and N=9  Pair (1,9) satisfies the above condition 1*9+1+9= “19” and only x=1 satisfies the equation.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible