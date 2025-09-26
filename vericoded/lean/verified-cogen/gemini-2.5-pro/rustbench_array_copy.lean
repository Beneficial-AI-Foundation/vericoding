import Mathlib
-- <vc-preamble>
@[reducible, simp]
def arrayCopy_precond (a : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- No helper lemmas needed as the proof is straightforward with existing simp lemmas.
-- </vc-helpers>

-- <vc-definitions>
def arrayCopy (a : Array Int) (h_precond : arrayCopy_precond (a)) : Array Int :=
  a.map id
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arrayCopy_postcond (a : Array Int) (result: Array Int) (h_precond : arrayCopy_precond (a)) :=
  result.size = a.size ∧ (∀ i, i < a.size → result[i]! = a[i]!)

theorem arrayCopy_spec_satisfied (a: Array Int) (h_precond : arrayCopy_precond (a)) :
    arrayCopy_postcond (a) (arrayCopy (a) h_precond) h_precond := by
  simp [arrayCopy, arrayCopy_postcond, Array.map_id]
-- </vc-theorems>
