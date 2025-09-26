import Mathlib
-- <vc-preamble>
def ValidInput (A B C : Int) : Prop :=
  0 ≤ A ∧ A ≤ 50 ∧ 0 ≤ B ∧ B ≤ 50 ∧ 0 ≤ C ∧ C ≤ 50

def MaxOf3 (A B C : Int) : Int :=
  if A ≥ B ∧ A ≥ C then A
  else if B ≥ C then B
  else C

def SortDescending (A B C : Int) : (Int × Int × Int) :=
  if A ≥ B ∧ A ≥ C then
    if B ≥ C then (A, B, C) else (A, C, B)
  else if B ≥ A ∧ B ≥ C then
    if A ≥ C then (B, A, C) else (B, C, A)
  else
    if A ≥ B then (C, A, B) else (C, B, A)

def MinOperations (A B C : Int) (h : ValidInput A B C) : Int :=
  let (a0, a1, a2) := SortDescending A B C
  let gap1 := a0 - a1
  let updated_smallest := a2 + gap1
  let remaining_gap := a0 - updated_smallest
  gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2

def AllEqual (A B C : Int) : Prop :=
  A = B ∧ B = C

@[reducible, simp]
def solve_precond (A B C : Int) : Prop :=
  ValidInput A B C
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma minOperations_nonneg (A B C : Int) (h : ValidInput A B C) : MinOperations A B C h ≥ 0 := by
  unfold MinOperations SortDescending
  split_ifs <;> simp <;> omega

-- LLM HELPER  
lemma minOperations_zero_when_equal (A B C : Int) (h : ValidInput A B C) (heq : AllEqual A B C) : 
    MinOperations A B C h = 0 := by
  unfold AllEqual at heq
  obtain ⟨hab, hbc⟩ := heq
  subst hab hbc
  unfold MinOperations SortDescending
  simp
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C : Int) (h_precond : solve_precond A B C) : Int :=
  MinOperations A B C h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C : Int) (result : Int) (h_precond : solve_precond A B C) : Prop :=
  result ≥ 0 ∧ (AllEqual A B C → result = 0) ∧ result = MinOperations A B C h_precond

theorem solve_spec_satisfied (A B C : Int) (h_precond : solve_precond A B C) :
    solve_postcond A B C (solve A B C h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · exact minOperations_nonneg A B C h_precond
  constructor
  · intro heq
    exact minOperations_zero_when_equal A B C h_precond heq
  · rfl
-- </vc-theorems>
