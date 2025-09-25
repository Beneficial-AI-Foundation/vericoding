-- <vc-preamble>
def my_min (x y : Nat) : Nat :=
  if x ≤ y then x else y

def ValidTestCase (a b n m : Nat) : Prop :=
  n + m > 0

def CanSatisfyAllGuests (a b n m : Nat) : Prop :=
  a + b ≥ n + m ∧ m ≤ my_min a b

@[reducible, simp]
def solve_precond (a b n m : Nat) : Prop :=
  ValidTestCase a b n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b n m : Nat) (h_precond : solve_precond a b n m) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b n m : Nat) (result : Bool) (h_precond : solve_precond a b n m) : Prop :=
  result = CanSatisfyAllGuests a b n m ∧
  (result → (a + b ≥ n + m ∧ m ≤ my_min a b)) ∧
  (¬result → (a + b < n + m ∨ m > my_min a b))

theorem solve_spec_satisfied (a b n m : Nat) (h_precond : solve_precond a b n m) :
    solve_postcond a b n m (solve a b n m h_precond) h_precond := by
  sorry
-- </vc-theorems>