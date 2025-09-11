-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find (arr : List Nat) (target : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_non_negative (arr : List Nat) (target : Nat) 
  (h : ∀ x ∈ arr, 0 < x) (h2 : arr ≠ []) : 
  0 ≤ find arr target :=
sorry

theorem find_zero_target (arr : List Nat) 
  (h : ∀ x ∈ arr, 0 < x) (h2 : arr ≠ []) :
  find arr 0 = 0 :=
sorry

theorem find_small_target (arr : List Nat) (target : Nat)
  (h : ∀ x ∈ arr, 0 < x) (h2 : arr ≠ []) 
  (h3 : ∀ x ∈ arr, target < x) :
  find arr target = 0 :=
sorry

theorem find_permutation_equivalent (arr₁ arr₂ : List Nat) (target : Nat)
  (h : ∀ x ∈ arr₁, 0 < x) (h2 : arr₁ ≠ [])
  (h3 : List.length arr₁ = List.length arr₂) 
  (h4 : ∀ x, List.count x arr₁ = List.count x arr₂) :
  find arr₁ target = find arr₂ target :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find [1, 2, 3] 5

/-
info: 5
-/
-- #guard_msgs in
-- #eval find [3, 6, 9, 12] 12

/-
info: 3
-/
-- #guard_msgs in
-- #eval find [1, 4, 5, 8] 8
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded