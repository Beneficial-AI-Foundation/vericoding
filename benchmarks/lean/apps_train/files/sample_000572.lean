Vasya has ordered a pizza delivery. The pizza can be considered a perfect circle. There were $n$ premade cuts in the pizza when it was delivered. Each cut is a straight segment connecting the center of the pizza with its boundary.
Let $O$ be the center of the pizza, $P_i$ be the endpoint of the $i$-th cut lying on the boundary, and $R$ be the point of the boundary straight to the right of $O$. Then the counterclockwise-measured angle $\angle ROP_i$ is equal to $a_i$ degrees, where $a_i$ is an integer between $0$ and $359$. Note that angles between $0$ and $180$ angles correspond to $P_i$ in the top half of the pizza, while angles between $180$ and $360$ angles correspond to the bottom half.
Vasya may cut his pizza a few more times, and the new cuts still have to be straight segments starting at the center. He wants to make the pizza separated into several equal slices, with each slice being a circular sector with no cuts inside of it. How many new cuts Vasya will have to make?

-----Input:-----
The first line of input contains $T$ , i.e number of test cases per file.
The first line of each test case contains a single integer $n-$  the numbers of premade cuts ($2 \leq n \leq 360$).
The second lines contains $n$ integers $a_1, \ldots, a_n-$ angles of the cuts $1, \ldots, n$ respectively ($0 \leq a_1 < \ldots, a_{n - 1} < 360$).

-----Output:-----
Print a single integer$-$ the smallest number of additional cuts Vasya has to make so that the pizza is divided into several equal slices.

-----Constraints-----
- $1  \leq T  \leq 36$
- $2 \leq n \leq 360$
- $0 \leq a_1 < \ldots, a_{n - 1} < 360$

-----Sample Input:-----
3
4 
0 90 180 270
2
90 210
2
0 1

-----Sample Output:-----
0
1
358

-----EXPLANATION:-----
In the first sample the pizza is already cut into four equal slices.
In the second sample the pizza will be cut into three equal slices after making one extra cut at $330$ degrees.
In the third sample Vasya will have to cut his pizza into $360$ pieces of $1$ degree angle each.

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def gcd (a b : Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
