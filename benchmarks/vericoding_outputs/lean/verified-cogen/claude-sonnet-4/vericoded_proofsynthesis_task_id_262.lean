import Mathlib
-- <vc-preamble>
@[reducible, simp]
def splitArray_precond (list : Array Int) (l : Nat) : Prop :=
  list.size > 0 ∧ 0 < l ∧ l < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: lemmas for array take/drop operations
lemma Array.toList_take (a : Array α) (n : Nat) : (a.take n).toList = List.take n a.toList := by
  simp [Array.take]

lemma Array.toList_drop (a : Array α) (n : Nat) : (a.drop n).toList = List.drop n a.toList := by
  simp [Array.drop]
-- </vc-helpers>

-- <vc-definitions>
def splitArray (list : Array Int) (l : Nat) (h_precond : splitArray_precond list l) : Array Int × Array Int :=
  (list.take l, list.drop l)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def splitArray_postcond (list : Array Int) (l : Nat) (result: Array Int × Array Int) (h_precond : splitArray_precond list l) : Prop :=
  result.1.toList = list.toList.take l ∧ result.2.toList = list.toList.drop l

theorem splitArray_spec_satisfied (list: Array Int) (l: Nat) (h_precond : splitArray_precond list l) :
    splitArray_postcond list l (splitArray list l h_precond) h_precond := by
  unfold splitArray_postcond splitArray
  simp [Array.toList_take, Array.toList_drop]
-- </vc-theorems>

def main : IO Unit := pure ()