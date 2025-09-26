import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidInput (n r : Int) : Prop :=
  n ≥ 1 ∧ r ≥ 1

def ExpectedResult (n r : Int) (h : ValidInput n r) : Int :=
  let k := if r < n - 1 then r else n - 1
  k * (k + 1) / 2 + (if r ≥ n then 1 else 0)

@[reducible, simp]
def solve_precond (n r : Int) : Prop :=
  ValidInput n r
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
lemma if_lt_is_min (a b : Int) : (if a < b then a else b) = min a b := by
  by_cases h : a < b
  · simp [h, min_eq_left (le_of_lt h)]
  · simp [h, min_eq_right (le_of_not_lt h)]

-- </vc-helpers>

-- <vc-definitions>
def solve (n r : Int) (h_precond : solve_precond n r) : Int :=
  let k := min r (n - 1)
  k * (k + 1) / 2 + (if r ≥ n then 1 else 0)
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
