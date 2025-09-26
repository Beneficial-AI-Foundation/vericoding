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

-- LLM HELPER
/-- An instance to make `BothCanTake` automatically decidable by the compiler.
    This lets us use it directly in an `if` expression. -/
instance (a b : Int) : Decidable (BothCanTake a b) := by
  unfold BothCanTake CanTakeNonAdjacent
  -- We need to prove `Decidable (a ≤ 16 / 2 ∧ b ≤ 16 / 2)`.
  -- Lean's type class inference can handle `Decidable (a ≤ 8 ∧ b ≤ 8)`
  -- but doesn't automatically reduce `16 / 2`.
  -- `simp_rw` can rewrite the goal using a proven equality.
  simp_rw [show (16 / 2 : Int) = 8 by norm_num]
  infer_instance

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
  unfold solve
  split_ifs with h_both_can_take
  . simp_all [solve_postcond]
  . simp_all [solve_postcond]
-- </vc-theorems>
