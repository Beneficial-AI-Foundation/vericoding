/-
Chef wants to organize a contest. Predicting difficulty levels of the problems can be a daunting task. Chef wants his contests to be balanced in terms of difficulty levels of the problems.
Assume a contest had total P participants. A problem that was solved by at least half of the participants (i.e. P / 2 (integer division)) is said to be cakewalk difficulty. A problem solved by at max P / 10 (integer division) participants is categorized to be a hard difficulty.
Chef wants the contest to be balanced. According to him, a balanced contest must have exactly 1 cakewalk and exactly 2 hard problems. You are given the description of N problems and the number of participants solving those problems. Can you tell whether the contest was balanced or not?

-----Input-----
The first line of the input contains an integer T denoting the number of test cases.
The first line of each test case contains two space separated integers, N, P denoting the number of problems, number of participants respectively.
The second line contains N space separated integers, i-th of which denotes number of participants solving the i-th problem.

-----Output-----
For each test case, output "yes" or "no" (without quotes) denoting whether the contest is balanced or not.

-----Constraints-----
- 1 ≤ T, N ≤ 500 
- 1 ≤ P ≤ 108 
- 1 ≤ Number of participants solving a problem ≤ P

-----Subtasks-----
- Subtask #1 (40 points): P is a multiple of 10
- Subtask #2 (60 points): Original constraints

-----Example-----
Input
6
3 100
10 1 100
3 100
11 1 100
3 100
10 1 10
3 100
10 1 50
4 100
50 50 50 50
4 100
1 1 1 1

Output
yes
no
no
yes
no
no

-----Explanation-----
Example case 1.: The problems are of hard, hard and cakewalk difficulty. There is 1 cakewalk and 2 hard problems, so the contest is balanced.
Example case 2.: The second problem is hard and the third is cakewalk. There is 1 cakewalk and 1 hard problem, so the contest is not balanced.
Example case 3.: All the three problems are hard. So the contest is not balanced.
Example case 4.: The problems are of hard, hard, cakewalk difficulty. The contest is balanced.
Example case 5.: All the problems are cakewalk. The contest is not balanced.
Example case 6.: All the problems are hard. The contest is not balanced.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_balanced_contest (n : Nat) (p : Nat) (solved_counts : List Nat) : String :=
  sorry

theorem is_balanced_contest_valid_output (n : Nat) (p : Nat) (solved_counts : List Nat) 
    (h1 : p ≥ 10) (h2 : p ≤ 10000) (h3 : solved_counts.length ≥ 3) (h4 : solved_counts.length ≤ 1000) :
  let result := is_balanced_contest n p solved_counts
  result = "yes" ∨ result = "no" :=
sorry

theorem is_balanced_contest_yes_conditions (n : Nat) (p : Nat) (solved_counts : List Nat)
    (h1 : p ≥ 10) (h2 : p ≤ 10000) (h3 : solved_counts.length ≥ 3) (h4 : solved_counts.length ≤ 1000)
    (h5 : is_balanced_contest n p solved_counts = "yes") :
  let cakewalk := solved_counts.filter (fun x => x ≥ p/2)
  let hard := solved_counts.filter (fun x => x ≤ p/10)
  cakewalk.length = 1 ∧ hard.length = 2 :=
sorry

theorem is_balanced_contest_all_same (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/4, p/4, p/4] = "no" :=
sorry

theorem is_balanced_contest_no_hard (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/2, p/2, p/2] = "no" :=
sorry

theorem is_balanced_contest_no_cakewalk (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/10, p/10, p/10] = "no" :=
sorry

theorem is_balanced_contest_perfect_case (p : Nat) (h : p ≥ 10) (h2 : p ≤ 10000) :
  is_balanced_contest 3 p [p/10, p/10, p/2] = "yes" :=
sorry

/-
info: 'yes'
-/
-- #guard_msgs in
-- #eval is_balanced_contest 3 100 [10, 1, 100]

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval is_balanced_contest 3 100 [11, 1, 100]

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval is_balanced_contest 4 100 [50, 50, 50, 50]

-- Apps difficulty: interview
-- Assurance level: unguarded