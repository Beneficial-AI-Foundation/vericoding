-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def josephus_survivor (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem josephus_bounds {n k : Nat} (h1 : n > 0) (h2 : k > 0) : 
  1 ≤ josephus_survivor n k ∧ josephus_survivor n k ≤ n := by
  sorry

theorem josephus_k_one {n : Nat} (h : n > 0) :
  josephus_survivor n 1 = n := by
  sorry

theorem josephus_n_one {k : Nat} (h : k > 0) :
  josephus_survivor 1 k = 1 := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval josephus_survivor 7 3

/-
info: 10
-/
-- #guard_msgs in
-- #eval josephus_survivor 11 19

/-
info: 28
-/
-- #guard_msgs in
-- #eval josephus_survivor 40 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded