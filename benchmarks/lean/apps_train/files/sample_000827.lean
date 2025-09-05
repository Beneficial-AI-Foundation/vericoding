Coach Moony wants the best team to represent their college in ICPC. He has $N$ students standing in a circle with certain rating $X_i$ on a competitive coding platform. It is an established fact that any coder with more rating on the platform is a better coder.      
Moony  wants to send his best $3$ coders based upon their rating. But all coders only want to have their friends in their team and every coder is friends with four other coders, adjacent two on left side in the circle, and adjacent two on right. So Moony comes up with a solution that team with maximum cumulative rating of all three members in a team shall be representing their college.
You need to give the cumulative score of the team that will be representing the college.

-----Input:-----
- First line will contain $T$, number of testcases. 
- First line of each test case contains a single integer $N$.
- Second  line of each test case takes $N$ integers, denoting rating of $ith$ coder.

-----Output:-----
For each testcase, output a single integer denoting cumulative rating  of the team.

-----Constraints-----
- $1 \leq T \leq 10$
- $7 \leq N \leq 10^5$ 
- $0 \leq X_i \leq 10^9$

-----Sample Input:-----
1

7

10 40 30 30 20 0 0  

-----Sample Output:-----
100

def find_max_team_score (n : Nat) (ratings : List Nat) : Nat := sorry

def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
