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
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : String) (h_precond : solve_precond a b) : Prop :=
  (BothCanTake a b ↔ result = "Yay!") ∧ 
  (¬BothCanTake a b ↔ result = ":(") ∧ 
  (result = "Yay!" ∨ result = ":(")

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>