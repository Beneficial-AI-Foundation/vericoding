/-
One upon a time there were three best friends Abhinav, Harsh, and Akash decided to form a 
team and take part in ICPC from KIIT. Participants are usually offered several problems during 
the programming contest. Long before the start, the friends decided that they will implement a 
problem if at least two of them are sure about the solution. Otherwise, friends won't write the 
problem's solution. 
This contest offers $N$ problems to the participants. For each problem we know, which friend is 
sure about the solution. Help the KIITians find the number of problems for which they will write a 
solution. 
Then n lines contain three integers each, each integer is either 0 or 1. If the first number in the 
line equals 1, then Abhinav is sure about the problem's solution, otherwise, he isn't sure. The 
second number shows Harsh's view on the solution, the third number shows Akash's view. The 
numbers on the lines are 

-----Input:-----
- A single integer will contain $N$, number of problems. 

-----Output:-----
Print a single integer — the number of problems the friends will implement on the contest. 

-----Constraints-----
- $1 \leq N \leq 1000$ 

-----Sample Input:-----
3

1 1 0

1 1 1

1 0 0   

-----Sample Output:-----
2  

-----EXPLANATION:-----
In the first sample, Abhinav and Harsh are sure that they know how to solve the first problem 
and all three of them know how to solve the second problem. That means that they will write 
solutions for these problems. Only Abhinav is sure about the solution for the third problem, but 
that isn't enough, so the group won't take it.
-/

-- <vc-helpers>
-- </vc-helpers>

def count_solved_problems (N: Nat) (confidence_matrix: List (List Nat)) : Nat :=
sorry

theorem count_solved_problems_non_negative {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≥ 0 :=
sorry

theorem count_solved_problems_upper_bound {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≤ confidence_matrix.length :=
sorry

theorem count_solved_problems_matches_confident {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix = 
    (confidence_matrix.filter (fun conf => (conf.foldl (· + ·) 0) ≥ 2)).length :=
sorry

theorem count_solved_problems_empty {N: Nat} :
  count_solved_problems N [] = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_solved_problems 3 [[1, 1, 0], [1, 1, 1], [1, 0, 0]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_solved_problems 4 [[1, 1, 1], [0, 0, 0], [1, 1, 0], [0, 1, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_solved_problems 2 [[0, 0, 0], [1, 0, 0]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible