-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def q (x : Nat) (y : Nat) : Nat :=
sorry

def strange : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem q_spec (x y : Nat) :
y - x > 2 → ∃ z, x < z*z ∧ z*z < y :=
sorry

theorem strange_spec :
1 = 2 :=
sorry
-- </vc-theorems>