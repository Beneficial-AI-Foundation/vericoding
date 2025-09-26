-- <vc-preamble>
def ValidInput (n m : Nat) (buttons : List (List Nat)) : Prop :=
  buttons.length = n ∧
  n ≥ 1 ∧ m ≥ 1 ∧
  ∀ i, 0 ≤ i ∧ i < n → ∀ j, 0 ≤ j ∧ j < buttons[i]!.length → 1 ≤ buttons[i]![j]! ∧ buttons[i]![j]! ≤ m

def unionOfAllBulbs (buttons : List (List Nat)) : List Nat :=
  buttons.foldl (fun acc button => acc ++ button) []

def CanTurnOnAllBulbs (m : Nat) (buttons : List (List Nat)) : Prop :=
  (unionOfAllBulbs buttons).eraseDups.length = m

@[reducible, simp]
def solve_precond (n m : Nat) (buttons : List (List Nat)) : Prop :=
  ValidInput n m buttons
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Nat) (buttons : List (List Nat)) (h_precond : solve_precond n m buttons) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Nat) (buttons : List (List Nat)) (result : String) (h_precond : solve_precond n m buttons) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ CanTurnOnAllBulbs m buttons)

theorem solve_spec_satisfied (n m : Nat) (buttons : List (List Nat)) (h_precond : solve_precond n m buttons) :
    solve_postcond n m buttons (solve n m buttons h_precond) h_precond := by
  sorry
-- </vc-theorems>