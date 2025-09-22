-- <vc-preamble>
def ValidInput (n a b : Int) (mobs : List Int) : Prop :=
  n ≥ 0 ∧ a > 0 ∧ b > 0 ∧ mobs.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < n → (mobs[i.natAbs]!) ≥ 0

def ValidOutput (result : List String) (n : Int) : Prop :=
  result.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < n → (result[i.natAbs]!) ∈ ["Vanya", "Vova", "Both"]

def determineWinner (k a b : Int) : Int :=
  if k ≤ a then 0
  else if k ≤ a + b then 1
  else 2

def CorrectResult (result : List String) (n a b : Int) (mobs : List Int) : Prop :=
  ValidOutput result n ∧
  ∀ i, 0 ≤ i ∧ i < n → 
    let total := a + b
    let k := if (mobs[i.natAbs]!) = 0 then 0 else (mobs[i.natAbs]!) % total
    ((result[i.natAbs]!) = "Vanya" ↔ determineWinner k a b = 0) ∧
    ((result[i.natAbs]!) = "Vova" ↔ determineWinner k a b = 1) ∧
    ((result[i.natAbs]!) = "Both" ↔ determineWinner k a b = 2)

@[reducible, simp]
def solve_precond (n a b : Int) (mobs : List Int) : Prop :=
  ValidInput n a b mobs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b : Int) (mobs : List Int) (h_precond : solve_precond n a b mobs) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b : Int) (mobs : List Int) (result : List String) (h_precond : solve_precond n a b mobs) : Prop :=
  CorrectResult result n a b mobs

theorem solve_spec_satisfied (n a b : Int) (mobs : List Int) (h_precond : solve_precond n a b mobs) :
    solve_postcond n a b mobs (solve n a b mobs h_precond) h_precond := by
  sorry
-- </vc-theorems>