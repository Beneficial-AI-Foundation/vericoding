def abs (n : Int) : Int :=
  sorry

def sum (lst : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def modified_sum (lst : List Int) (p : Nat) : Int :=
  sorry

theorem modified_sum_p_one {lst : List Int} (h : lst ≠ []) : 
  modified_sum lst 1 = 0 := sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval modified_sum [1, 2, 3] 3

/-
info: 30
-/
-- #guard_msgs in
-- #eval modified_sum [1, 2] 5

/-
info: 68
-/
-- #guard_msgs in
-- #eval modified_sum [3, 5, 7] 2

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible