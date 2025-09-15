-- <vc-preamble>
@[reducible, simp]
def isDivisible (n : Int) (divisor : Int) : Bool :=
  n % divisor = 0

@[reducible, simp]
def primeNum_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Main function for testing -/
def main : IO Unit := do
  pure ()