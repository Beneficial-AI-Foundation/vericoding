import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def IntDiv (m : Int) (n : Int) : Int × Int :=
if h : n > 0 then (m.ediv n, m.emod n) else (0, 0)
-- </vc-definitions>

-- <vc-theorems>
theorem IntDiv_spec (m n : Int) :
n > 0 →
let (d, r) := IntDiv m n
m = n * d + r ∧ 0 ≤ r ∧ r < n :=
by
  intro hn
  have h1 : m = n * (m.ediv n) + m.emod n := by
    simpa using (Int.ediv_add_emod m n).symm
  have h2 : 0 ≤ m.emod n := by
    have hne : n ≠ 0 := ne_of_gt hn
    simpa using (Int.emod_nonneg m hne)
  have h3 : m.emod n < n := by
    simpa using (Int.emod_lt_of_pos m hn)
  simpa [IntDiv, hn] using And.intro h1 (And.intro h2 h3)
-- </vc-theorems>
