-- <vc-preamble>
/- Define the triangular number function -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + triangle n

/- Precondition for tail_triangle function -/
@[reducible, simp]
def tailTriangle_precond (n : Nat) (idx : Nat) (sum : Nat) : Prop :=
  idx ≤ n ∧ sum = triangle idx ∧ triangle n < 0x100000000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()