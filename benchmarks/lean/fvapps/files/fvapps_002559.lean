-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bubble (lst : List Int) : List (List Int) :=
sorry

def isSorted (lst : List Int) : Bool :=
sorry

def countInversions (lst : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bubble_steps_are_permutations {lst : List Int} {step : List Int} :
  step ∈ bubble lst → step.length = lst.length :=
sorry

theorem bubble_steps_have_swaps {lst : List Int} {i : Nat} (h1 : i < (bubble lst).length) (h2 : i + 1 < (bubble lst).length) :
  ∃ pos : Nat, pos < lst.length ∧
    ((bubble lst).get ⟨i, h1⟩).get! pos ≠ ((bubble lst).get ⟨i+1, h2⟩).get! pos :=
sorry

theorem bubble_final_step_sorted {lst : List Int} (h : bubble lst ≠ []) :
  isSorted ((bubble lst).getLast h) :=
sorry

theorem bubble_steps_bounded_by_inversions {lst : List Int} :
  (bubble lst).length ≤ countInversions lst :=
sorry

theorem bubble_sorted_empty {lst : List Int} :
  isSorted lst → bubble lst = [] :=
sorry

theorem bubble_empty :
  bubble [] = [] :=
sorry
-- </vc-theorems>