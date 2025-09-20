-- <vc-preamble>
def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | x :: xs => match xs with
    | [] => true
    | y :: _ => x ≤ y && isSorted xs

def isSortedBy {α : Type} (l : List α) (f : α → α → Bool) : Bool :=
  match l with
  | [] => true
  | x :: xs => match xs with
    | [] => true
    | y :: _ => f x y && isSortedBy xs f
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_zero_sum_groups (arr : List Int) (n : Nat) : String ⊕ List Int ⊕ List (List Int) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_array_returns_no_elements {n : Nat} (h : n > 0) :
  find_zero_sum_groups [] n = Sum.inl "No elements to combine" :=
sorry

theorem valid_solution_has_correct_length {arr : List Int} {n : Nat} {result : List Int}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inl result)) :
  result.length = n :=
sorry

theorem valid_solution_sums_to_zero {arr : List Int} {n : Nat} {result : List Int}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inl result)) :
  result.foldl (· + ·) 0 = 0 :=
sorry

theorem valid_solution_elements_in_input {arr : List Int} {n : Nat} {result : List Int}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inl result)) :
  ∀ x ∈ result, x ∈ arr :=
sorry

theorem valid_solution_is_sorted {arr : List Int} {n : Nat} {result : List Int}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inl result)) :
  isSorted result = true :=
sorry

theorem multiple_solutions_all_valid {arr : List Int} {n : Nat} {results : List (List Int)}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inr results)) :
  ∀ result ∈ results,
    result.length = n ∧
    result.foldl (· + ·) 0 = 0 ∧
    (∀ x ∈ result, x ∈ arr) ∧
    isSorted result = true :=
sorry

theorem multiple_solutions_are_sorted {arr : List Int} {n : Nat} {results : List (List Int)}
  (h : find_zero_sum_groups arr n = Sum.inr (Sum.inr results)) :
  isSortedBy results (fun x y => x.foldl (· + ·) 0 ≤ y.foldl (· + ·) 0) = true :=
sorry

theorem all_positive_has_no_solution {arr : List Int} {n : Nat}
  (h1 : ∀ x ∈ arr, x > 0)
  (h2 : n > 0)
  (h3 : n ≤ arr.length) :
  find_zero_sum_groups arr n = Sum.inl "No combinations" :=
sorry

theorem size_larger_than_array_no_solution {arr : List Int} {n : Nat}
  (h : n > arr.length) :
  find_zero_sum_groups arr n = Sum.inl "No combinations" :=
sorry
-- </vc-theorems>