-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_steps_to_arrange (n : Nat) (positions : List Nat) : Nat :=
  sorry

-- Any array of all zeros returns 0 steps
-- </vc-definitions>

-- <vc-theorems>
theorem all_zeros {n : Nat} (h : n > 0) :
  min_steps_to_arrange n (List.replicate n 0) = 0 :=
sorry

-- Steps returned are always non-negative (this is implied by Nat return type)
-- but stating it explicitly for clarity

theorem steps_non_negative {n : Nat} (positions : List Nat) : 
  min_steps_to_arrange n positions ≥ 0 :=
sorry

-- Positions can only reference valid indices

theorem valid_positions {n : Nat} (positions : List Nat) :
  List.length positions = n →
  ∀ i, i < n → (positions.get ⟨i, sorry⟩ = 0 ∨ positions.get ⟨i, sorry⟩ ≤ i) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_steps_to_arrange 1 [0]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_steps_to_arrange 3 [0, 0, 0]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_steps_to_arrange 5 [0, 1, 2, 1, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded