-- <vc-preamble>
def length_sup_u_k (n : Nat) (k : Nat) : Nat :=
  sorry

def comp (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def u1 : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_sup_u_k_bounds (n k : Nat) (h : n > 0) :
  0 ≤ length_sup_u_k n k ∧ length_sup_u_k n k ≤ n :=
  sorry

theorem comp_bounds (n : Nat) (h : n > 1) :
  0 ≤ comp n ∧ comp n ≤ n - 1 :=
  sorry

theorem comp_deterministic (n : Nat) :
  comp n = comp n :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval length_sup_u_k 23 12

/-
info: 35
-/
-- #guard_msgs in
-- #eval length_sup_u_k 50 10

/-
info: 304
-/
-- #guard_msgs in
-- #eval length_sup_u_k 500 100

/-
info: 1
-/
-- #guard_msgs in
-- #eval comp 23

/-
info: 22
-/
-- #guard_msgs in
-- #eval comp 100

/-
info: 63
-/
-- #guard_msgs in
-- #eval comp 200
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible