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
-- </vc-theorems>