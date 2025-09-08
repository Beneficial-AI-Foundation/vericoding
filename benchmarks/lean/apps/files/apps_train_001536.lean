/-
Consider a currency system in which there are notes of six denominations, namely, Rs. 1, Rs. 2, Rs. 5, Rs. 10, Rs. 50, Rs. 100.
If the sum of Rs. N is input, write a program to computer smallest number of notes that will combine to give Rs. N.

-----Input-----

The first line contains an integer T, total number of testcases. Then follow T lines, each line contains an integer N. 

-----Output-----
For each test case, display the smallest number of notes that will combine to give N, in a new line.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ N ≤ 1000000

-----Example-----
Input
3 
1200
500
242

Output
12
5
7
-/

-- <vc-helpers>
-- </vc-helpers>

def min_notes_needed (amount : Nat) : Nat :=
  sorry

theorem min_notes_needed_nonnegative (amount : Nat) : 
  min_notes_needed amount ≥ 0 :=
  sorry

theorem min_notes_needed_exact_change (amount : Nat) :
  let notes := [100, 50, 10, 5, 2, 1]
  let count := min_notes_needed amount
  let remainingAndCount := notes.foldl 
    (fun (acc : Nat × Nat) (note : Nat) => 
      let remaining := acc.1
      let count := acc.2
      let notes_used := remaining / note
      (remaining - notes_used * note, count + notes_used))
    (amount, 0)
  count = remainingAndCount.2 ∧ remainingAndCount.1 = 0 :=
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval min_notes_needed 1200

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_notes_needed 500

/-
info: 7
-/
-- #guard_msgs in
-- #eval min_notes_needed 242

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible