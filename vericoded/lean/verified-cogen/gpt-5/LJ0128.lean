import Mathlib
-- <vc-preamble>
/- Helper function to compute sum of a list recursively -/
def sumTo : List Int → Int
  | [] => 0  
  | xs => 
    if h : xs = [] then 0 
    else 
      have h_len : xs.length - 1 < xs.length := by
        have : xs.length > 0 := by
          cases xs with
          | nil => simp at h
          | cons _ _ => simp
        omega
      sumTo (xs.dropLast) + xs.getLast!
termination_by xs => xs.length

@[reducible, simp]
def sum_precond (arr : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma sumTo_nil : sumTo ([] : List Int) = 0 := by
  simp [sumTo]
-- </vc-helpers>

-- <vc-definitions>
def sum (arr : Array Int) (h_precond : sum_precond arr) : Int :=
  sumTo arr.toList
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sum_postcond (arr : Array Int) (result : Int) (h_precond : sum_precond arr) : Prop :=
  sumTo (arr.toList) = result

theorem sum_spec_satisfied (arr : Array Int) (h_precond : sum_precond arr) :
    sum_postcond arr (sum arr h_precond) h_precond := by
  simp [sum_postcond, sum]
-- </vc-theorems>

/- Test cases and examples can be added here -/