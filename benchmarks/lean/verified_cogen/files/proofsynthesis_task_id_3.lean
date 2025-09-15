-- <vc-preamble>
-- Specification function for divisibility check
def isDivisible (n : Int) (divisor : Int) : Bool :=
  n % divisor = 0

-- Precondition for isNonPrime
@[reducible, simp]
def isNonPrime_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  pure ()