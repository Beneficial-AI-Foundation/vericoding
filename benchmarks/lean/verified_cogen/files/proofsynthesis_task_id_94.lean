-- <vc-preamble>
@[reducible, simp]
def minSecondValueFirst_precond (arr : Array (Array Int)) :=
  arr.size > 0 ∧ (∀ i, i < arr.size → arr[i]!.size ≥ 2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minSecondValueFirst (arr : Array (Array Int)) (h_precond : minSecondValueFirst_precond arr) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def minSecondValueFirst_postcond (arr : Array (Array Int)) (first_of_min_second : Int) (h_precond : minSecondValueFirst_precond arr) :=
  ∃ i, i < arr.size ∧ first_of_min_second = arr[i]![0]! ∧ (∀ j, j < arr.size → arr[i]![1]! ≤ arr[j]![1]!)

theorem minSecondValueFirst_spec_satisfied (arr : Array (Array Int)) (h_precond : minSecondValueFirst_precond arr) :
    minSecondValueFirst_postcond arr (minSecondValueFirst arr h_precond) h_precond := by
  sorry
-- </vc-theorems>