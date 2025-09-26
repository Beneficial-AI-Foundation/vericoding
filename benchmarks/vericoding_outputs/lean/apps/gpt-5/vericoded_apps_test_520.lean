import Mathlib
-- <vc-preamble>
def sumRange (s : List Int) (start : Nat) (end_ : Nat) : Int :=
  if start >= end_ then 
    0
  else if start >= s.length then
    0
  else 
    s[start]! + sumRange s (start + 1) end_

def ValidInput (n : Int) (years : List Int) : Prop :=
  n > 0 ∧ years.length = n.natAbs

@[reducible, simp]
def solve_precond (n : Int) (years : List Int) : Prop :=
  ValidInput n years
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma sumRange_of_start_ge_end (s : List Int) (start end_ : Nat) (h : start ≥ end_) :
  sumRange s start end_ = 0 := by
  simpa [sumRange, h]

-- LLM HELPER
@[simp] lemma sumRange_empty_right (s : List Int) :
  sumRange s s.length s.length = 0 := by
  simpa using sumRange_of_start_ge_end s s.length s.length (le_rfl)

-- LLM HELPER
lemma pos_of_valid {n : Int} {years : List Int} (h : ValidInput n years) : n > 0 := h.left

-- LLM HELPER
lemma length_eq_natAbs_of_valid {n : Int} {years : List Int} (h : ValidInput n years) :
  years.length = n.natAbs := h.right

-- LLM HELPER
lemma n_ne_zero_of_valid {n : Int} {years : List Int} (h : ValidInput n years) : n ≠ 0 :=
  ne_of_gt h.left
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (years : List Int) (h_precond : solve_precond n years) : Int :=
  sumRange years 0 years.length / n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (years : List Int) (result : Int) (h_precond : solve_precond n years) : Prop :=
  result = sumRange years 0 years.length / n

theorem solve_spec_satisfied (n : Int) (years : List Int) (h_precond : solve_precond n years) :
    solve_postcond n years (solve n years h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
