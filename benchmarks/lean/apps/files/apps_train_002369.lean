/-
Given two non-negative integers low and high. Return the count of odd numbers between low and high (inclusive).

Example 1:
Input: low = 3, high = 7
Output: 3
Explanation: The odd numbers between 3 and 7 are [3,5,7].
Example 2:
Input: low = 8, high = 10
Output: 1
Explanation: The odd numbers between 8 and 10 are [9].

Constraints:

0 <= low <= high <= 10^9
-/

-- <vc-helpers>
-- </vc-helpers>

def count_odds (low high : Int) : Nat :=
  sorry

theorem count_odds_correct (low high : Int) (h : high ≥ low) (h2 : high - low < 1000) :
  count_odds low high = ((List.range (Int.toNat (high - low + 1))).filter (fun n => (Int.ofNat n + low) % 2 ≠ 0)).length :=
  sorry

theorem count_odds_single_number (n : Int) :
  count_odds n n = if n % 2 = 0 then 0 else 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_odds 3 7

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_odds 8 10

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_odds 0 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible