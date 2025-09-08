/-
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
-/

def find_max_team_score (n : Nat) (ratings : List Nat) : Nat := sorry

def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs

-- <vc-helpers>
-- </vc-helpers>

def take_last (n : Nat) (l : List Nat) : List Nat := 
  let rev := l.reverse
  (rev.take n).reverse

theorem find_max_team_score_upper_bound 
  (ratings : List Nat) (h : ratings.length ≥ 3) :
  find_max_team_score ratings.length ratings ≤ list_sum (take_last 3 ratings) := sorry

theorem find_max_team_score_lower_bound 
  (ratings : List Nat) (h : ratings.length ≥ 3) : 
  find_max_team_score ratings.length ratings ≥ list_sum (ratings.take 3) := sorry

theorem find_max_team_score_three_elements
  (ratings : List Nat) (h : ratings.length = 3) :
  find_max_team_score ratings.length ratings = list_sum ratings := sorry

theorem find_max_team_score_consecutive
  (ratings : List Nat) (h : ratings.length ≥ 3) (i : Nat) (hi : i + 2 < ratings.length) :
  find_max_team_score ratings.length ratings ≥ 
    ratings[i]! + ratings[i+1]! + ratings[i+2]! := sorry

theorem find_max_team_score_wrapping
  (ratings : List Nat) (h : ratings.length ≥ 3) (i : Nat) :
  find_max_team_score ratings.length ratings ≥
    ratings[i % ratings.length]! + 
    ratings[(i + 1) % ratings.length]! + 
    ratings[(i + 2) % ratings.length]! := sorry

theorem find_max_team_score_all_equal
  (n : Nat) (h : n ≥ 3) :
  find_max_team_score n (List.replicate n 1) = 3 := sorry

/-
info: 100
-/
-- #guard_msgs in
-- #eval find_max_team_score 7 [10, 40, 30, 30, 20, 0, 0]

/-
info: 100
-/
-- #guard_msgs in
-- #eval find_max_team_score 7 [50, 20, 30, 10, 40, 15, 25]

/-
info: 60
-/
-- #guard_msgs in
-- #eval find_max_team_score 3 [10, 20, 30]

-- Apps difficulty: interview
-- Assurance level: unguarded