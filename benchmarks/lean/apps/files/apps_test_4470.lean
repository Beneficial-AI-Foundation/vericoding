-- <vc-preamble>
def ValidInput (n : Nat) : Prop :=
  n > 0

def ReduceByFactors235 : Nat → Nat
| 0 => 0
| 1 => 1
| n + 1 => 
  let m := n + 1
  if m % 2 = 0 then ReduceByFactors235 (m / 2)
  else if m % 3 = 0 then ReduceByFactors235 (m / 3)
  else if m % 5 = 0 then ReduceByFactors235 (m / 5)
  else m

def OnlyFactors235 (n : Nat) : Prop :=
  n > 0 ∧ ReduceByFactors235 n = 1

def CanReachOne (n : Nat) : Prop :=
  n > 0 ∧ OnlyFactors235 n

def MinMovesToOne : Nat → Nat
| 0 => 0
| 1 => 0
| n + 1 => 
  let m := n + 1
  if m % 2 = 0 then 1 + MinMovesToOne (m / 2)
  else if m % 3 = 0 then 2 + MinMovesToOne (m / 3)
  else if m % 5 = 0 then 3 + MinMovesToOne (m / 5)
  else 0

@[reducible, simp]
def solve_precond (n : Nat) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ -1 ∧ 
  (result = -1 ↔ ¬CanReachOne n) ∧
  (result ≥ 0 → CanReachOne n ∧ result = MinMovesToOne n)

theorem solve_spec_satisfied (n : Nat) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>