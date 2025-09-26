import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 16 ∧ 1 ≤ b ∧ b ≤ 16 ∧ a + b ≤ 16

def CanTakeNonAdjacent (pieces total : Int) : Prop :=
  pieces ≤ total / 2

def BothCanTake (a b : Int) : Prop :=
  CanTakeNonAdjacent a 16 ∧ CanTakeNonAdjacent b 16

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: decidable instance and lemmas
instance : Decidable (BothCanTake a b) := by
  unfold BothCanTake CanTakeNonAdjacent
  infer_instance

lemma bothCanTake_iff (a b : Int) : BothCanTake a b ↔ a ≤ 8 ∧ b ≤ 8 := by
  unfold BothCanTake CanTakeNonAdjacent
  simp only [show (16 : Int) / 2 = 8 by norm_num]

lemma solve_cases (a b : Int) (h_precond : solve_precond a b) :
    (a ≤ 8 ∧ b ≤ 8) ∨ ¬(a ≤ 8 ∧ b ≤ 8) := by
  by_cases h : a ≤ 8 ∧ b ≤ 8
  · left; exact h
  · right; exact h
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : String :=
  if BothCanTake a b then "Yay!" else ":("

-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : String) (h_precond : solve_precond a b) : Prop :=
  (BothCanTake a b ↔ result = "Yay!") ∧ 
  (¬BothCanTake a b ↔ result = ":(") ∧ 
  (result = "Yay!" ∨ result = ":(")

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · constructor
    · intro h_both
      simp [h_both]
    · intro h_eq
      by_contra h_not_both
      simp [h_not_both] at h_eq
  constructor
  · constructor
    · intro h_not_both
      simp [h_not_both]
    · intro h_eq
      by_contra h_both
      simp [h_both] at h_eq
  · by_cases h : BothCanTake a b
    · left; simp [h]
    · right; simp [h]
-- </vc-theorems>
