-- <vc-preamble>
def listSum : List Int → Int
  | [] => 0
  | h :: t => h + listSum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumNested : List (List Int) → Int :=
  sorry

def flatten : List (List Int) → List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_nested_equals_flatten_sum (l : List (List Int)) :
  sumNested l = listSum (flatten l) := by
  sorry

theorem sum_nested_empty_lists (l : List (List Int)) (h : ∀ x ∈ l, x = []) :
  sumNested l = 0 := by
  sorry

theorem sum_nested_singleton (n : Int) :
  sumNested [[n]] = n := by
  sorry
-- </vc-theorems>