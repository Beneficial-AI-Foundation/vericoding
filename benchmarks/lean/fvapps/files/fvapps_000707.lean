-- <vc-preamble>
def count_char (c : Char) (s : List Char) : Nat :=
  (s.filter (fun x => x = c)).length

def sum_list : List Nat → Nat
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_meals (ingredients : List (List Char)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_meals_non_negative (ingredients : List (List Char)) :
  max_meals ingredients ≥ 0 := by
sorry

theorem max_meals_bounded_by_c (ingredients : List (List Char)) :
  max_meals ingredients ≤ (sum_list (ingredients.map (count_char 'c'))) / 2 := by
sorry

theorem max_meals_bounded_by_o (ingredients : List (List Char)) :
  max_meals ingredients ≤ sum_list (ingredients.map (count_char 'o')) := by
sorry

theorem max_meals_bounded_by_d (ingredients : List (List Char)) :
  max_meals ingredients ≤ sum_list (ingredients.map (count_char 'd')) := by
sorry

theorem max_meals_bounded_by_e (ingredients : List (List Char)) :
  max_meals ingredients ≤ (sum_list (ingredients.map (count_char 'e'))) / 2 := by
sorry

theorem max_meals_bounded_by_h (ingredients : List (List Char)) :
  max_meals ingredients ≤ sum_list (ingredients.map (count_char 'h')) := by
sorry

theorem max_meals_bounded_by_f (ingredients : List (List Char)) :
  max_meals ingredients ≤ sum_list (ingredients.map (count_char 'f')) := by
sorry

theorem max_meals_empty_list :
  max_meals [] = 0 := by
sorry

theorem max_meals_doubles (ingredients : List (List Char)) :
  ingredients ≠ [] →
  max_meals (ingredients.map (fun s => s ++ s)) ≥ max_meals ingredients := by
sorry

theorem max_meals_with_invalid_chars (ingredients : List (List Char)) :
  max_meals ingredients ≥ 0 := by
sorry
-- </vc-theorems>