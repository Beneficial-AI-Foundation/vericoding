-- <vc-preamble>
def ValidInput (coins : List Int) : Prop :=
  coins.length = 5 ∧ ∀ i, 0 ≤ i ∧ i < coins.length → 0 ≤ coins[i]! ∧ coins[i]! ≤ 100

def TotalCoins (coins : List Int) : Int :=
  coins[0]! + coins[1]! + coins[2]! + coins[3]! + coins[4]!

def HasValidSolution (coins : List Int) : Prop :=
  ValidInput coins ∧ 
  let total := TotalCoins coins
  total > 0 ∧ total % 5 = 0

def ComputeResult (coins : List Int) : Int :=
  let total := TotalCoins coins
  if total > 0 ∧ total % 5 = 0 then total / 5 else -1

@[reducible, simp]
def solve_precond (coins : List Int) : Prop :=
  ValidInput coins
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (coins : List Int) (h_precond : solve_precond coins) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (coins : List Int) (result : Int) (h_precond : solve_precond coins) : Prop :=
  result = ComputeResult coins ∧ 
  (HasValidSolution coins → result = TotalCoins coins / 5) ∧
  (¬HasValidSolution coins → result = -1)

theorem solve_spec_satisfied (coins : List Int) (h_precond : solve_precond coins) :
    solve_postcond coins (solve coins h_precond) h_precond := by
  sorry
-- </vc-theorems>