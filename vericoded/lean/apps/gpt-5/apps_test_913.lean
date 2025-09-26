import Mathlib
-- <vc-preamble>
def ValidInput (n : Nat) (r : List Int) (b : List Int) : Prop :=
  n > 0 ∧ r.length = n ∧ b.length = n ∧
  (∀ i, i < n → r.get! i = 0 ∨ r.get! i = 1) ∧
  (∀ i, i < n → b.get! i = 0 ∨ b.get! i = 1)

def RobotAdvantageCount (n : Nat) (r : List Int) (b : List Int) : Nat :=
  (List.range n).filter (fun i => r.get! i = 1 ∧ b.get! i = 0) |>.length

def OpponentAdvantageCount (n : Nat) (r : List Int) (b : List Int) : Nat :=
  (List.range n).filter (fun i => r.get! i = 0 ∧ b.get! i = 1) |>.length

def CanWin (n : Nat) (r : List Int) (b : List Int) : Bool :=
  RobotAdvantageCount n r b > 0

def MinMaxPointValue (n : Nat) (r : List Int) (b : List Int) : Int :=
  (OpponentAdvantageCount n r b : Int) / (RobotAdvantageCount n r b : Int) + 1

@[reducible, simp]
def solve_precond (n : Nat) (r : List Int) (b : List Int) : Prop :=
  ValidInput n r b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (r : List Int) (b : List Int) (h_precond : solve_precond n r b) : Int :=
  if CanWin n r b then MinMaxPointValue n r b else -1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (r : List Int) (b : List Int) (result : Int) (h_precond : solve_precond n r b) : Prop :=
  if CanWin n r b then result = MinMaxPointValue n r b else result = -1

theorem solve_spec_satisfied (n : Nat) (r : List Int) (b : List Int) (h_precond : solve_precond n r b) :
    solve_postcond n r b (solve n r b h_precond) h_precond := by
  unfold solve_postcond solve; cases h : CanWin n r b <;> simp [h]
-- </vc-theorems>
