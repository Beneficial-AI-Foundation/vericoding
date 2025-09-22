-- <vc-preamble>
def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_number (l : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_number_length {l : List Int} (h : l ≠ []) :
  (sort_number l).length = l.length :=
sorry

theorem sort_number_first {l : List Int} (h : l ≠ []) :
  (sort_number l).head! = 1 :=
sorry

theorem sort_number_deterministic {l : List Int} (h : l ≠ []) :
  sort_number l = sort_number l :=
sorry
-- </vc-theorems>