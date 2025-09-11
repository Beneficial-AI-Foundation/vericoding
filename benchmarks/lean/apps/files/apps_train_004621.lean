-- <vc-preamble>
def find_difference (a b : List Nat) : Nat := sorry

def list_prod (l : List Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat := 
  if n ≥ 0 then n else 0
-- </vc-definitions>

-- <vc-theorems>
theorem find_difference_non_negative (a b : List Nat) (h₁ : a ≠ []) (h₂ : b ≠ []) :
  find_difference a b ≥ 0 := sorry

theorem find_difference_symmetry (a b : List Nat) (h₁ : a ≠ []) (h₂ : b ≠ []) :
  find_difference a b = find_difference b a := sorry

theorem find_difference_identity (a : List Nat) (h : a ≠ []) :
  find_difference a a = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_difference [2, 2, 3] [5, 4, 1]

/-
info: 14
-/
-- #guard_msgs in
-- #eval find_difference [3, 2, 5] [1, 4, 4]

/-
info: 106
-/
-- #guard_msgs in
-- #eval find_difference [9, 7, 2] [5, 2, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible