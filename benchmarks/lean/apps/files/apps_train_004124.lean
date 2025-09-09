-- <vc-helpers>
-- </vc-helpers>

def int_rac (n : Nat) (guess : Nat) : Nat :=
  sorry

theorem int_rac_perfect_squares_consistency (x : Nat)
  (h1 : x ≥ 1) (h2 : x ≤ 20) :
  let n := x * x
  let guess1 := max 1 (x - 1) 
  let guess2 := x + 1
  Nat.sub (int_rac n guess1) (int_rac n guess2) ≤ 1 ∧ 
  Nat.sub (int_rac n guess2) (int_rac n guess1) ≤ 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval int_rac 25 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_rac 125348 300

/-
info: 3
-/
-- #guard_msgs in
-- #eval int_rac 125348981764 356243

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible