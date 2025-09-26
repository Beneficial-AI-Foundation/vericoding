import Mathlib
-- <vc-preamble>
def ValidInput (lst : List Int) : Prop :=
  5 ≤ lst.length ∧ lst.length ≤ 10 ∧
  ∀ i, 0 ≤ i ∧ i < lst.length → 1 ≤ lst[i]! ∧ lst[i]! ≤ 32

def int_xor (a b : Int) : Int :=
  Int.ofNat (a.natAbs ^^^ b.natAbs)

def min_of_sequence (s : List Int) : Int :=
  s.foldl min s[0]!

@[reducible, simp]
def solve_precond (lst : List Int) : Prop :=
  ValidInput lst
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma min_of_sequence_def (s : List Int) :
  min_of_sequence s = s.foldl min s[0]! := rfl

-- LLM HELPER
@[simp] lemma solve_precond_iff (lst : List Int) :
  solve_precond lst ↔ ValidInput lst := Iff.rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (lst : List Int) (h_precond : solve_precond lst) : Int :=
  2 + int_xor lst[2]! (min_of_sequence lst)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (lst : List Int) (result : Int) (h_precond : solve_precond lst) : Prop :=
  result = 2 + int_xor lst[2]! (min_of_sequence lst)

theorem solve_spec_satisfied (lst : List Int) (h_precond : solve_precond lst) :
    solve_postcond lst (solve lst h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>
