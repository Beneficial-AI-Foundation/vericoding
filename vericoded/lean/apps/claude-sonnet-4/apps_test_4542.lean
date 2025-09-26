import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.get (String.Pos.mk i) = 'B' ∨ s.get (String.Pos.mk i) = 'W'

def CountSegments (s : String) : Nat := s.length

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemmas for string length arithmetic
lemma string_length_pos_of_valid {s : String} (h : ValidInput s) : s.length > 0 := h.1

lemma string_length_sub_one_nonneg {s : String} (h : ValidInput s) : (s.length : Int) - 1 ≥ 0 := by
  have h_pos : s.length > 0 := string_length_pos_of_valid h
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  (s.length : Int) - 1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  result ≥ 0 ∧ result = (CountSegments s : Int) - 1 ∧ result ≤ (s.length : Int) - 1

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- result ≥ 0
    have h_pos : s.length > 0 := h_precond.1
    omega
  constructor
  · -- result = (CountSegments s : Int) - 1
    unfold CountSegments
    rfl
  · -- result ≤ (s.length : Int) - 1
    rfl
-- </vc-theorems>
