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
lemma valid_input_length (lst : List Int) (h : ValidInput lst) : 0 < lst.length := by
  obtain ⟨h_lower, _⟩ := h
  omega

-- LLM HELPER
lemma valid_input_index_two (lst : List Int) (h : ValidInput lst) : 2 < lst.length := by
  obtain ⟨h_lower, _⟩ := h
  omega

-- LLM HELPER
lemma valid_input_nonempty (lst : List Int) (h : ValidInput lst) : lst ≠ [] := by
  intro h_empty
  have h_len := valid_input_length lst h
  rw [h_empty] at h_len
  simp at h_len
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
