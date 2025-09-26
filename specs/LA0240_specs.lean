-- <vc-preamble>
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by gcd a b => b

def ValidInput (r b k : Int) : Prop :=
  r > 0 ∧ b > 0 ∧ k > 0

def MaxConsecutiveSameColor (r b : Int) : Int :=
  let a := Int.min r b
  let b_val := Int.max r b
  let n := Int.ofNat (gcd a.natAbs b_val.natAbs)
  -((n - b_val) / a)

def CanAvoidConsecutive (r b k : Int) : Bool :=
  if r > 0 ∧ b > 0 ∧ k > 0 then MaxConsecutiveSameColor r b < k else false

@[reducible, simp]
def solve_precond (r b k : Int) : Prop :=
  ValidInput r b k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (r b k : Int) (_ : solve_precond r b k) : String :=
  if CanAvoidConsecutive r b k then "OBEY" else "REBEL"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (r b k : Int) (result : String) (_ : solve_precond r b k) : Prop :=
  result = (if CanAvoidConsecutive r b k then "OBEY" else "REBEL")

theorem solve_spec_satisfied (r b k : Int) (h_precond : solve_precond r b k) :
    solve_postcond r b k (solve r b k h_precond) h_precond := by
  simp [solve, solve_postcond]
-- </vc-theorems>