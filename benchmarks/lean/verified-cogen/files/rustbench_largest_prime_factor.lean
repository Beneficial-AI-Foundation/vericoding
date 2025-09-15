-- <vc-preamble>
/- Specification predicate to check if a number is prime -/
@[reducible, simp]
def isPrimePred (n : Nat) : Prop :=
  ∀ k : Nat, 2 ≤ k → k < n → n % k ≠ 0

/- Precondition for largestPrimeFactor function -/
@[reducible, simp]
def largestPrimeFactor_precond (n : Nat) : Prop :=
  2 ≤ n ∧ n ≤ 4294967294
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  IO.println "Main function"