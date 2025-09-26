import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def IntDiv (m : Int) (n : Int) : Int × Int :=
(m / n, m % n)
-- </vc-definitions>

-- <vc-theorems>
theorem IntDiv_spec (m n : Int) :
n > 0 →
let (d, r) := IntDiv m n
m = n * d + r ∧ 0 ≤ r ∧ r < n :=
by
  intro hn
  simp [IntDiv]
  refine' ⟨(Int.ediv_add_emod m n).symm, _, _⟩
  · exact Int.emod_nonneg m (ne_of_gt hn)
  · exact Int.emod_lt_of_pos m hn
-- </vc-theorems>
