-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_recipe_valid (n : Nat) (lst : List Nat) : String := sorry

theorem recipe_validation_output_is_yes_or_no (n : Nat) (lst : List Nat) :
  let result := check_recipe_valid n lst
  result = "YES" ∨ result = "NO" := sorry

-- For recipes marked valid:
-- </vc-definitions>

-- <vc-theorems>
theorem valid_recipe_elements_appear_contiguously (n : Nat) (lst : List Nat) :
  let result := check_recipe_valid n lst
  result = "YES" →
  ∀ i j k : Nat, 
    i < j ∧ j < k ∧ k < lst.length →
    lst[i]! = lst[k]! → 
    lst[i]! = lst[j]! := sorry

theorem valid_recipe_frequencies_unique (n : Nat) (lst : List Nat) :
  let result := check_recipe_valid n lst
  result = "YES" →
  ∀ x y : Nat,
    x ∈ lst → y ∈ lst →
    x ≠ y →
    (lst.filter (λ i => i = x)).length ≠ (lst.filter (λ i => i = y)).length := sorry

theorem single_ingredient_recipe_always_valid (n : Nat) (x : Nat) :
  let lst := List.replicate n x
  check_recipe_valid n lst = "YES" := sorry

theorem discontinuous_ingredient_invalid (n : Nat) (lst : List Nat) (x : Nat) :
  lst.length ≥ 2 →
  x ∈ lst →
  let discontinuous := lst ++ [x]
  (∀ i j : Nat, i < j → j < lst.length → lst[i]! = lst[j]! → i + 1 = j) →
  check_recipe_valid (lst.length + 1) discontinuous = "NO" := sorry
-- </vc-theorems>