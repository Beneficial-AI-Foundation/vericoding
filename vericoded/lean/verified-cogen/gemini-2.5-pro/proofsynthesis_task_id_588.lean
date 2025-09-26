import Mathlib
-- <vc-preamble>
def maxInt (a b : Int) : Int := if a ≥ b then a else b
def minInt (a b : Int) : Int := if a ≤ b then a else b

def maxRcur : List Int → Int
  | [] => 0
  | [x] => x
  | xs => maxInt xs.getLast! (maxRcur xs.dropLast)
termination_by xs => xs.length
decreasing_by
  simp_wf
  sorry

def minRcur : List Int → Int
  | [] => 0
  | [x] => x
  | xs => minInt xs.getLast! (minRcur xs.dropLast)
termination_by xs => xs.length
decreasing_by
  simp_wf
  sorry

@[reducible, simp]
def differenceMaxMin_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → (-2147483648 / 2) < arr[i]! ∧ arr[i]! < (2147483647 / 2))
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
theorem maxInt_eq_max (a b : Int) : maxInt a b = max a b := by
  unfold maxInt
  rw [max_def]
  split_ifs <;> linarith

-- LLM HELPER
theorem minInt_eq_min (a b : Int) : minInt a b = min a b := by
  unfold minInt
  rw [min_def]

-- </vc-helpers>

-- <vc-definitions>
def differenceMaxMin (arr : Array Int) (h_precond : differenceMaxMin_precond arr) : Int :=
    maxRcur arr.toList - minRcur arr.toList

-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def differenceMaxMin_postcond (arr : Array Int) (diff : Int) (h_precond : differenceMaxMin_precond arr) : Prop :=
  diff = maxRcur arr.toList - minRcur arr.toList

theorem differenceMaxMin_spec_satisfied (arr : Array Int) (h_precond : differenceMaxMin_precond arr) :
    differenceMaxMin_postcond arr (differenceMaxMin arr h_precond) h_precond := by
    simp [differenceMaxMin_postcond, differenceMaxMin]

-- </vc-theorems>
