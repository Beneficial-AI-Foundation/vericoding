-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def five_by_2n (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem five_by_2n_positive (n : Nat) : 
  n > 0 → five_by_2n n > 0 :=
  sorry

theorem five_by_2n_bounded (n : Nat) :
  n > 0 → five_by_2n n < 12345787 :=
  sorry 

theorem five_by_2n_deterministic (n : Nat) :
  five_by_2n n = five_by_2n n :=
  sorry

theorem five_by_2n_sequential (n : Nat) :
  n > 0 → True :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval five_by_2n 1

/-
info: 95
-/
-- #guard_msgs in
-- #eval five_by_2n 2

/-
info: 1183
-/
-- #guard_msgs in
-- #eval five_by_2n 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible