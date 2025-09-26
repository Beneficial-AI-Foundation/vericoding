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
-- LLM HELPER: Lemmas about ValidInput guaranteeing list access safety
lemma ValidInput.length_ge_five {lst : List Int} (h : ValidInput lst) : 5 ≤ lst.length := h.1

lemma ValidInput.length_le_ten {lst : List Int} (h : ValidInput lst) : lst.length ≤ 10 := h.2.1

lemma ValidInput.index_two_valid {lst : List Int} (h : ValidInput lst) : 2 < lst.length := by
  have h_len := ValidInput.length_ge_five h
  omega

lemma ValidInput.index_zero_valid {lst : List Int} (h : ValidInput lst) : 0 < lst.length := by
  have h_len := ValidInput.length_ge_five h
  omega
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
  unfold solve_postcond solve
  rfl
-- </vc-theorems>
