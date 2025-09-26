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
lemma maxRcur_singleton (x : Int) : maxRcur [x] = x := by
  unfold maxRcur
  rfl

-- LLM HELPER
lemma minRcur_singleton (x : Int) : minRcur [x] = x := by
  unfold minRcur
  rfl

-- LLM HELPER
lemma maxInt_ge_left (a b : Int) : a ≤ maxInt a b := by
  unfold maxInt
  split_ifs with h
  · exact le_refl a
  · exact le_of_not_ge h

-- LLM HELPER
lemma maxInt_ge_right (a b : Int) : b ≤ maxInt a b := by
  unfold maxInt
  split_ifs with h
  · exact h
  · exact le_refl b

-- LLM HELPER
lemma minInt_le_left (a b : Int) : minInt a b ≤ a := by
  unfold minInt
  split_ifs with h
  · exact le_refl a
  · exact le_of_not_ge h

-- LLM HELPER
lemma minInt_le_right (a b : Int) : minInt a b ≤ b := by
  unfold minInt
  split_ifs with h
  · exact h
  · exact le_refl b
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
  unfold differenceMaxMin_postcond differenceMaxMin
  simp
-- </vc-theorems>

def main : IO Unit := pure ()