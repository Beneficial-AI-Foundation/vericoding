There are $N$ buckets numbered $1$ through $N$. The buckets contain balls; each ball has a color between $1$ and $K$. Let's denote the number of balls with color $j$ that are initially in bucket $i$ by $a_{i, j}$.
For each $i$ from $1$ to $N-1$ (in this order), someone draws a ball uniformly at random from bucket $i$ and puts it into bucket $i+1$, then continues to draw the next ball. After putting a ball in bucket $N$, this person draws a ball, again uniformly at random, from bucket $N$.
For each color from $1$ to $K$, find the probability that the ball drawn from bucket $N$ has this color.

-----Input-----
- The first line of the input contains two space-separated integers $N$ and $K$. 
- $N$ lines follow. For each $i$ ($1 \le i \le N$), the $i$-th of these lines contains $K$ space-separated integers $a_{i, 1}, a_{i, 2}, \ldots, a_{i, K}$.

-----Output-----
Print a single line containing $K$ space-separated real numbers. For each valid $i$, the $i$-th of these numbers should denote the probability that the last drawn ball has color $i$. your answer will be considered correct if absolute or relative error does not exceed $10^{-6}$

-----Constraints-----
- $1 \le N, K \le 1,000$
- $0 \le a_{i, j} \le 10$ for each valid $i, j$
- initially, there is at least one ball in bucket $1$

-----Subtasks-----
Subtask #1 (30 points): $1 \le N, K \le 100$
Subtask #2 (70 points): original constraints

-----Example Input-----
2 2
0 1
1 1

-----Example Output-----
0.333333 0.666667

-----Explanation-----

def solve_bucket_probability (N K : Nat) (arr : List (List Nat)) : List Float := sorry

def sum_float (xs : List Float) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded