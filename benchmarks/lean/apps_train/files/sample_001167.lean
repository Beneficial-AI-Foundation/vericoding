Chef is solving mathematics problems. He is preparing for Engineering Entrance exam. He's stuck in a problem.
$f(n)=1^n*2^{n-1}*3^{n-2} * \ldots * n^{1} $ 
Help Chef to find the value of $f(n)$.Since this number could be very large, compute it modulo $1000000007$.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input,  $N$. 

-----Output:-----
For each testcase, output in a single line the value of $f(n)$ mod $1000000007$.

-----Constraints-----
- $1 \leq T \leq 10^6$
- $1 \leq N \leq 10^6$

-----Subtasks-----
Subtask 1(24 points) : 
- $1 \leq T \leq 5000$
- $1 \leq N \leq 5000$
Subtask 2(51 points) : original constraints

-----Sample Input:-----
1
3

-----Sample Output:-----
12

def MOD := 1000000007

def solve_f_n (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
