import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def IsArmstrong (n : Int) : Bool :=
let d1 := n / 100
  let d2 := (n / 10) % 10
  let d3 := n % 10
  n == d1 * d1 * d1 + d2 * d2 * d2 + d3 * d3 * d3
-- </vc-definitions>

-- <vc-theorems>
theorem IsArmstrong_spec (n : Int) :
100 ≤ n ∧ n < 1000 →
IsArmstrong n = (n = ((n / 100) * (n / 100) * (n / 100) +
((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
(n % 10) * (n % 10) * (n % 10))) :=
by
  intro ⟨h_lower, h_upper⟩
  unfold IsArmstrong
  simp only [BEq.beq, decide_eq_true_iff]
-- </vc-theorems>
