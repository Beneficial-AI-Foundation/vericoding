import Mathlib
-- <vc-preamble>
/- Helper functions for recursively computing max and min of a list -/
def maxRcur (seq : List Int) : Int :=
  match seq with
  | [] => 0  /- Should not happen given preconditions -/
  | [x] => x
  | x :: xs => max x (maxRcur xs)

def minRcur (seq : List Int) : Int :=
  match seq with
  | [] => 0  /- Should not happen given preconditions -/
  | [x] => x  
  | x :: xs => min x (minRcur xs)

@[reducible, simp]
def sumMinMax_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ ∀ i, i < arr.size → -1073741824 < arr[i]! ∧ arr[i]! < 1073741823
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma maxRcur_singleton (x : Int) : maxRcur [x] = x := rfl
-- LLM HELPER
@[simp] lemma minRcur_singleton (x : Int) : minRcur [x] = x := rfl
-- </vc-helpers>

-- <vc-definitions>
def sumMinMax (arr : Array Int) (h_precond : sumMinMax_precond arr) : Int :=
  maxRcur arr.toList + minRcur arr.toList
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def sumMinMax_postcond (arr : Array Int) (sum : Int) (h_precond : sumMinMax_precond arr) : Prop :=
  sum = maxRcur arr.toList + minRcur arr.toList

theorem sumMinMax_spec_satisfied (arr : Array Int) (h_precond : sumMinMax_precond arr) :
    sumMinMax_postcond arr (sumMinMax arr h_precond) h_precond := by
  rfl
-- </vc-theorems>
