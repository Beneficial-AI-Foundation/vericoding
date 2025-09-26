-- <vc-preamble>
def sumList (l : List Nat) : Nat :=
  l.foldl (·+·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum_steps (arr : List Nat) (n : Nat) : Option Nat :=
  sorry

def List.sort (l : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimum_steps_nonnegative (arr : List Nat) (n : Nat)
  (h : minimum_steps arr n ≠ none) :
  ∀ result, minimum_steps arr n = some result → result ≥ 0 :=
sorry

theorem minimum_steps_less_than_length (arr : List Nat) (n : Nat)
  (h : minimum_steps arr n ≠ none) :
  ∀ result, minimum_steps arr n = some result → result < arr.length :=
sorry

theorem minimum_steps_sum_sufficient (arr : List Nat) (n : Nat)
  (h : minimum_steps arr n ≠ none) :
  ∀ result, minimum_steps arr n = some result →
  sumList (List.take (result + 1) (arr.sort)) ≥ n :=
sorry

theorem minimum_steps_sum_necessary (arr : List Nat) (n : Nat)
  (h : minimum_steps arr n ≠ none) :
  ∀ result, minimum_steps arr n = some result →
  result > 0 → sumList (List.take result (arr.sort)) < n :=
sorry

theorem minimum_steps_sort_invariant (arr : List Nat) (n : Nat) :
  minimum_steps (arr.sort) n = minimum_steps arr n :=
sorry

theorem minimum_steps_single_element_target_le (x : Nat) (n : Nat) :
  n ≤ x → minimum_steps [x] n = some 0 :=
sorry

theorem minimum_steps_first_element_sufficient (x y z : Nat) :
  minimum_steps [x, y, z] y = some 0 :=
sorry
-- </vc-theorems>