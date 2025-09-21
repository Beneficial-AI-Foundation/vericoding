-- <vc-preamble>
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b
decreasing_by simp_wf; apply Nat.mod_lt; omega

def lcm (a b : Nat) : Nat :=
  (a * b) / gcd a b

def lcmSeq (nums : List Nat) : Nat :=
  match nums with
  | [] => 1
  | [x] => x
  | x :: xs => lcm x (lcmSeq xs)

def ValidInput (periods : List Nat) : Prop :=
  periods.length > 0 ∧ periods.length ≤ 100 ∧
  ∀ i, 0 ≤ i ∧ i < periods.length → periods[i]! > 0

def CorrectResult (periods : List Nat) (result : Nat) : Prop :=
  result = lcmSeq periods

@[reducible, simp]
def solve_precond (periods : List Nat) : Prop :=
  ValidInput periods
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (periods : List Nat) (h_precond : solve_precond periods) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (periods : List Nat) (result : Nat) (h_precond : solve_precond periods) : Prop :=
  CorrectResult periods result

theorem solve_spec_satisfied (periods : List Nat) (h_precond : solve_precond periods) :
    solve_postcond periods (solve periods h_precond) h_precond := by
  sorry
-- </vc-theorems>