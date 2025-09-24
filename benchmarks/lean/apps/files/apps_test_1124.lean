-- <vc-preamble>
def ValidInput (values : List Int) : Prop :=
  values.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < values.length → values[i]! > 0

def gcd (a b : Nat) : Nat :=
  if a = 0 then b
  else gcd (b % a) a
termination_by a
decreasing_by
  simp_wf
  exact Nat.mod_lt b (Nat.pos_of_ne_zero ‹a ≠ 0›)

def gcdSeq (values : List Nat) (index : Nat) (current : Nat) : Nat :=
  if index ≥ values.length then current
  else gcdSeq values (index + 1) (gcd current values[index]!)
termination_by values.length - index

def gcdOfAll (values : List Nat) : Nat :=
  if values.length = 0 then 1
  else gcdSeq values 1 values[0]!

@[reducible, simp]
def solve_precond (values : List Int) : Prop :=
  ValidInput values
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (values : List Int) (h_precond : solve_precond values) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (values : List Int) (result : Int) (h_precond : solve_precond values) : Prop :=
  result > 0 ∧ ∀ i, 0 ≤ i ∧ i < values.length → values[i]! % result = 0

theorem solve_spec_satisfied (values : List Int) (h_precond : solve_precond values) :
    solve_postcond values (solve values h_precond) h_precond := by
  sorry
-- </vc-theorems>