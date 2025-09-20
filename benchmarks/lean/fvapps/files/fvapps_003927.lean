-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubblesortOnce (xs : List Int) : List Int :=
  sorry

def isSorted (xs : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_same_length {xs : List Int} (h : xs ≠ []) :
  List.length (bubblesortOnce xs) = List.length xs :=
sorry

theorem input_unchanged {xs : List Int} (h : xs ≠ []) :
  let original := xs
  bubblesortOnce xs = bubblesortOnce original :=
sorry

theorem at_least_one_swap_if_unsorted {xs : List Int} (h : xs ≠ []) :
  List.length xs > 1 →
  ¬isSorted xs →
  bubblesortOnce xs ≠ xs :=
sorry

theorem moves_max_element_right {xs : List Int} (h : xs ≠ []) :
  List.length xs > 1 →
  let result := bubblesortOnce xs
  ∀ y ∈ List.take (List.length result - 1) result,
  y ≤ List.get! result (List.length result - 1) :=
sorry
-- </vc-theorems>