-- <vc-preamble>
def collatzLength (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestCollatz (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_collatz_is_member {nums : List Nat} (h : nums ≠ []) :
  ∀ n, n = longestCollatz nums → n ∈ nums :=
  sorry

theorem longest_collatz_is_longest {nums : List Nat} (h : nums.length ≥ 2) :
  ∀ n ∈ nums, n ≠ longestCollatz nums → 
    collatzLength (longestCollatz nums) ≥ collatzLength n :=
  sorry

theorem identical_numbers_gives_first (n : Nat) (l : List Nat) 
  (h : ∀ x ∈ l, x = n) :
  longestCollatz l = n :=
  sorry

/-
info: 27
-/
-- #guard_msgs in
-- #eval longest_collatz [1, 5, 27, 4]

/-
info: 27
-/
-- #guard_msgs in
-- #eval longest_collatz [64, 64, 27, 64]

/-
info: 75
-/
-- #guard_msgs in
-- #eval longest_collatz [75, 226, 113, 340]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded