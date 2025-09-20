-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_recipe_scores (recipes : List String) : String ⊕ Float := sorry

def Permutation (α : Type) (xs ys : List α) : Prop := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem recipe_scores_valid_output (recipes: List String) : 
  let result := calculate_recipe_scores recipes
  match result with
  | Sum.inl str => str = "Infinity"
  | Sum.inr num => 0 ≤ num ∧ num ≤ 10^7
  := sorry

theorem recipe_scores_consistent (recipes: List String) :
  let result1 := calculate_recipe_scores recipes
  let result2 := calculate_recipe_scores recipes
  match result1, result2 with
  | Sum.inl str1, Sum.inl str2 => str1 = str2
  | Sum.inr num1, Sum.inr num2 => (num1 - num2).abs < 0.000001
  | _, _ => False
  := sorry

theorem recipe_scores_order_invariant (recipes: List String) (perm: List String) :
  Permutation String recipes perm →
  let result1 := calculate_recipe_scores recipes
  let result2 := calculate_recipe_scores perm
  match result1, result2 with
  | Sum.inl str1, Sum.inl str2 => str1 = str2
  | Sum.inr num1, Sum.inr num2 => (num1 - num2).abs < 0.000001
  | _, _ => False
  := sorry
-- </vc-theorems>