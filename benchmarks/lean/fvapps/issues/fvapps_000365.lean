-- <vc-preamble>
def List.sum [Add α] (xs : List α) : α :=
  match xs with
  | [] => sorry
  | x :: xs => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_superstring (strings : List (List Char)) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem superstring_contains_all_inputs (strings : List (List Char)) 
  (h : strings ≠ []) : 
  ∀ s ∈ strings, ∃ i, strings.get ⟨i, sorry⟩ = s :=
sorry

theorem superstring_length_less_than_sum (strings : List (List Char))
  (h : strings ≠ []) :
  (shortest_superstring strings).length ≤ List.sum (strings.map List.length) :=
sorry

theorem superstring_handles_overlaps (strings : List (List Char)) 
  (h₁ : strings ≠ [])
  (h₂ : strings.length ≥ 2) :
  (shortest_superstring strings).length ≤ List.sum (strings.map List.length) :=
sorry

theorem superstring_identity_single (s : List Char) :
  shortest_superstring [s] = s :=
sorry

theorem superstring_basic_example :
  (shortest_superstring [['a','b','c'], ['b','c','d']]).length ≤ 4 :=
sorry
-- </vc-theorems>