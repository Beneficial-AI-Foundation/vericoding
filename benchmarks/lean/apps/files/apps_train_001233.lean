-- <vc-preamble>
def min_elements_needed (N K : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def permutation (l1 l2 : List Nat) : Prop :=
  l1.length = l2.length ∧ ∀ x, x ∈ l1 ↔ x ∈ l2
-- </vc-definitions>

-- <vc-theorems>
theorem min_elements_non_negative (N K : Nat) (arr : List Nat) :
  min_elements_needed N K arr ≥ 0 :=
  sorry

theorem min_elements_upper_bound (N K : Nat) (arr : List Nat) :
  min_elements_needed N K arr ≤ K :=
  sorry

theorem min_elements_complete_powers (N K : Nat) (arr : List Nat) :
  (∀ i : Nat, i < K → (2^i) ∈ arr) →
  min_elements_needed N K arr = 0 :=
  sorry

theorem min_elements_empty (K : Nat) :
  min_elements_needed 0 K [] = K :=
  sorry

theorem min_elements_singleton_min (K : Nat) :
  min_elements_needed 1 K [1] = K - 1 :=
  sorry

theorem min_elements_singleton_max (K : Nat) :
  min_elements_needed 1 K [2^K] = K :=
  sorry

theorem min_elements_perm_invariant (N K : Nat) (arr₁ arr₂ : List Nat) :
  permutation arr₁ arr₂ →
  min_elements_needed N K arr₁ = min_elements_needed N K arr₂ :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_elements_needed 2 2 [3, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_elements_needed 7 3 [3, 7, 5, 4, 6, 2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_elements_needed 1 3 [2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded