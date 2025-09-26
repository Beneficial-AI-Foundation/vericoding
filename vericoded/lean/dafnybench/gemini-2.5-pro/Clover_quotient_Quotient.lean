import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def Quotient_ (x : Nat) (y : Nat) : Int × Int :=
(↑(x % y), ↑(x / y))
-- </vc-definitions>

-- <vc-theorems>
theorem Quotient_spec (x : Nat) (y : Nat) :
y ≠ 0 →
let (r, q) := Quotient_ x y
q * y + r = x ∧ 0 ≤ r ∧ r < y ∧ 0 ≤ q :=
fun hy => by
  simp only [Quotient_]
  constructor
  · norm_cast
    rw [mul_comm]
    exact Nat.div_add_mod x y
  · constructor
    · positivity
    · constructor
      · norm_cast
        apply Nat.mod_lt
        exact Nat.pos_of_ne_zero hy
      · positivity
-- </vc-theorems>
