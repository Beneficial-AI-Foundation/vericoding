import Mathlib
-- <vc-preamble>
/- Precondition for count_true -/
@[reducible, simp]
def countTrue_precond (arr : Array Bool) : Prop := True

/- Helper function to count boolean values -/
def countBoolean (seq : List Bool) : Int :=
  match seq with
  | [] => 0
  | hd :: tl => countBoolean tl + if hd then 1 else 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma countBoolean_nonneg (l : List Bool) : 0 ≤ countBoolean l := by
  induction l with
  | nil => simp [countBoolean]
  | cons hd tl ih =>
    simp [countBoolean]
    split <;> linarith

-- LLM HELPER
lemma countBoolean_le_length (l : List Bool) : countBoolean l ≤ l.length := by
  induction l with
  | nil => simp [countBoolean]
  | cons hd tl ih =>
    simp [countBoolean, List.length]
    split
    · have h1 : countBoolean tl ≤ tl.length := ih
      linarith
    · have h2 : countBoolean tl ≤ tl.length := ih
      linarith

-- LLM HELPER
lemma countBoolean_eq_filter_length (l : List Bool) : countBoolean l = (l.filter id).length := by
  induction l with
  | nil => simp [countBoolean, List.filter]
  | cons hd tl ih =>
    simp [countBoolean, List.filter]
    by_cases h : hd
    · simp [h, ih]
    · simp [h, ih]
-- </vc-helpers>

-- <vc-definitions>
def countTrue (arr : Array Bool) (h_precond : countTrue_precond arr) : Nat :=
  arr.toList.filter id |>.length
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countTrue_postcond (arr : Array Bool) (count : Nat) (h_precond : countTrue_precond arr) : Prop :=
  0 ≤ count ∧ count ≤ arr.size ∧ countBoolean arr.toList = count

theorem countTrue_spec_satisfied (arr : Array Bool) (h_precond : countTrue_precond arr) :
    countTrue_postcond arr (countTrue arr h_precond) h_precond := by
  unfold countTrue_postcond countTrue
  constructor
  · exact Nat.zero_le _
  constructor
  · have h := List.length_filter_le id arr.toList
    rw [Array.size_eq_length_toList]
    exact h
  · exact countBoolean_eq_filter_length arr.toList
-- </vc-theorems>

/- Main function -/
def main : IO Unit := return ()