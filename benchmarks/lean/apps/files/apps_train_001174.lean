-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_ingredients (n : Nat) (x : Nat) (ingredients : List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_ingredients_valid_output (n : Nat) (x : Nat) (ingredients : List Nat) (h : ingredients ≠ []) : 
  check_ingredients n x ingredients = "YES" ∨ check_ingredients n x ingredients = "NO" :=
  sorry

theorem check_ingredients_expected_result (n : Nat) (x : Nat) (ingredients : List Nat) (h : ingredients ≠ []) :
  check_ingredients n x ingredients = "YES" ↔ ∃ i ∈ ingredients, i ≥ x :=
  sorry

theorem zero_threshold (n : Nat) (ingredients : List Nat) (h : ingredients ≠ []) (h2 : ∀ i ∈ ingredients, i > 0) :
  check_ingredients n 0 ingredients = "YES" :=
  sorry

theorem single_ingredient (n : Nat) (x : Nat) (ingredient : Nat) :
  check_ingredients n x [ingredient] = if ingredient ≥ x then "YES" else "NO" :=
  sorry

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval check_ingredients 5 100 [11, 22, 33, 44, 55]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval check_ingredients 5 50 [10, 20, 30, 40, 50]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval check_ingredients 5 45 [12, 24, 36, 48, 60]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded