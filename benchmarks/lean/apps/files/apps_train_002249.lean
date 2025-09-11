-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_multisets (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_multisets_result_bounds (n k : Nat) 
  (h1 : n > 0) (h2 : k ≤ n) : 
  count_multisets n k < 998244353 ∧ count_multisets n k ≥ 0 :=
  sorry

theorem count_multisets_k_equal_n (n k : Nat)
  (h1 : n > 0) (h2 : k = n) :
  count_multisets n k > 0 :=
  sorry

theorem count_multisets_known_values_1 :
  count_multisets 4 2 = 2 :=
  sorry

theorem count_multisets_known_values_2 :
  count_multisets 2525 425 = 687232272 :=
  sorry

theorem count_multisets_known_values_3 :
  count_multisets 3000 1 = 815951975 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_multisets 4 2

/-
info: 687232272
-/
-- #guard_msgs in
-- #eval count_multisets 2525 425

/-
info: 815951975
-/
-- #guard_msgs in
-- #eval count_multisets 3000 1
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible