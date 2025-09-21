-- <vc-preamble>

def ValidInput (n : Nat) (a : Nat) (x : List Int) : Prop :=
  n > 0 ∧ 1 ≤ a ∧ a ≤ n ∧ x.length = n ∧ 
  ∀ i, i < n → (x[i]! = 0 ∨ x[i]! = 1)

def SumCriminalsCaught (n : Nat) (a_idx : Nat) (x : List Int) (distance : Nat) : Int :=
  if distance > n then 0
  else
    let le := if a_idx ≥ distance then a_idx - distance else 0
    let rg := a_idx + distance
    let le_valid := a_idx ≥ distance ∧ le < n
    let rg_valid := rg < n
    let current_caught :=
      if ¬le_valid ∧ ¬rg_valid then 0
      else if le_valid ∧ ¬rg_valid then x[le]!
      else if ¬le_valid ∧ rg_valid then x[rg]!
      else if le_valid ∧ rg_valid ∧ x[le]! = 1 ∧ x[rg]! = 1 then 2
      else 0
    if ¬le_valid ∧ ¬rg_valid then current_caught
    else current_caught + SumCriminalsCaught n a_idx x (distance + 1)
termination_by n + 1 - distance

def TotalCriminalsCaught (n : Nat) (a : Nat) (x : List Int) : Int :=
  x[a-1]! + SumCriminalsCaught n (a-1) x 1

@[reducible, simp]
def solve_precond (n : Nat) (a : Nat) (x : List Int) : Prop :=
  ValidInput n a x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (a : Nat) (x : List Int) (h_precond : solve_precond n a x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (a : Nat) (x : List Int) (result : Int) (h_precond : solve_precond n a x) : Prop :=
  result ≥ 0 ∧ result = TotalCriminalsCaught n a x

theorem solve_spec_satisfied (n : Nat) (a : Nat) (x : List Int) (h_precond : solve_precond n a x) :
    solve_postcond n a x (solve n a x h_precond) h_precond := by
  sorry
-- </vc-theorems>