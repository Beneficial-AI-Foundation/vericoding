-- <vc-preamble>
def ValidInput (n m : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ a.length = n ∧ 
  (∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 1)

def ValidOutput (result : List Int) (n : Int) : Prop :=
  result.length = n ∧ (∀ i, 0 ≤ i ∧ i < result.length → result[i]! ≥ 0)

def ComputePageTurns (a : List Int) (m i s : Int) : Int :=
  if i ≥ a.length then 0
  else (s + a[Int.natAbs i]!) / m

def ComputeNextState (a : List Int) (m i s : Int) : Int :=
  if i ≥ a.length then s
  else (s + a[Int.natAbs i]!) % m

def ComputeStateAt (a : List Int) (m day : Int) : Int :=
  if day ≤ 0 then 0
  else if day > a.length then ComputeStateAt a m a.length
  else (ComputeStateAt a m (day - 1) + a[Int.natAbs (day - 1)]!) % m
termination_by Int.natAbs day

def CorrectPageTurns (result a : List Int) (m : Int) : Prop :=
  m ≥ 1 → 
  result.length = a.length ∧
  (∀ i, 0 ≤ i ∧ i < a.length → 
    let s := ComputeStateAt a m i
    result[Int.natAbs i]! = (s + a[Int.natAbs i]!) / m)

@[reducible, simp]
def solve_precond (n m : Int) (a : List Int) : Prop :=
  ValidInput n m a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (a : List Int) (h_precond : solve_precond n m a) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (a : List Int) (result : List Int) (h_precond : solve_precond n m a) : Prop :=
  ValidOutput result n ∧ CorrectPageTurns result a m

theorem solve_spec_satisfied (n m : Int) (a : List Int) (h_precond : solve_precond n m a) :
    solve_postcond n m a (solve n m a h_precond) h_precond := by
  sorry
-- </vc-theorems>