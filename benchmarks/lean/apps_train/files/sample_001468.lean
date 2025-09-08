/-
Zonal Computing Olympiad 2014, 30 Nov 2013

In IPL 2025, the amount that each player is paid varies from match to match.  The match fee depends on the quality of opposition, the venue etc.

The match fees for each match in the new season have been announced in advance.  Each team has to enforce a mandatory rotation policy so that no player ever plays three matches in a row during the season.

Nikhil is the captain and chooses the team for each match. He wants to allocate a playing schedule for himself to maximize his earnings through match fees during the season.  

-----Input format-----
Line 1: A single integer N, the number of games in the IPL season.
Line 2: N non-negative integers, where the integer in
position i represents the fee for match i.

-----Output format-----
The output consists of a single non-negative integer, the
maximum amount of money that Nikhil can earn during this IPL
season. 

-----Sample Input 1-----
5 
10 3 5 7 3 

-----Sample Output 1-----
23

(Explanation: 10+3+7+3)

-----Sample Input 2-----
8
3 2 3 2 3 5 1 3

-----Sample Output 2-----
17

(Explanation: 3+3+3+5+3)

-----Test data-----
There is only one subtask worth 100 marks.  In all inputs:

• 1 ≤ N ≤ 2×105
• The fee for each match is between 0 and 104, inclusive.

-----Live evaluation data-----
There are 12 test inputs on the server during the exam.
-/

def List.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + List.sum xs

def List.maximum' : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: xs => max x (List.maximum' xs)

/- Main function -/

-- <vc-helpers>
-- </vc-helpers>

def calculate_max_earnings (n : Nat) (fees : List Nat) : Nat :=
  sorry

/- Theorems -/

theorem calculate_max_earnings_bounded (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees ≤ fees.sum :=
  sorry

theorem calculate_max_earnings_nonnegative (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees ≥ 0 :=
  sorry

theorem calculate_max_earnings_returns_number (n : Nat) (fees : List Nat) :
  n > 0 → fees.length = n → calculate_max_earnings n fees = calculate_max_earnings n fees :=
  sorry

/-
info: 23
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 5 [10, 3, 5, 7, 3]

/-
info: 17
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 8 [3, 2, 3, 2, 3, 5, 1, 3]

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_max_earnings 3 [1, 2, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible