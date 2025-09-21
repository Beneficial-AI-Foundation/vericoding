-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Quotient_ (x : Nat) (y : Nat) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Quotient_spec (x : Nat) (y : Nat) :
y ≠ 0 →
let (r, q) := Quotient_ x y
q * y + r = x ∧ 0 ≤ r ∧ r < y ∧ 0 ≤ q :=
sorry
-- </vc-theorems>