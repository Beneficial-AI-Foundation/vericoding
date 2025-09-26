import Mathlib
-- <vc-preamble>
partial def comb (n : Nat) (k : Nat) : Nat :=
if k == 0 ∨ k == n then 1
else comb (n-1) k + comb (n-1) (k-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No auxiliary helpers required for this development.

-- </vc-helpers>

-- <vc-definitions>
def Comb (n : Nat) (k : Nat) : Nat :=
if k ≤ n then comb n k else 0

-- </vc-definitions>

-- <vc-theorems>
theorem Comb_spec (n : Nat) (k : Nat) :
0 ≤ k ∧ k ≤ n → Comb n k = comb n k :=
by
  intro ⟨_h0, hk⟩
  dsimp [Comb]
  simp [if_pos hk]

-- </vc-theorems>
