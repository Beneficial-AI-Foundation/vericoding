import Mathlib
-- <vc-preamble>
partial def comb (n : Nat) (k : Nat) : Nat :=
if k == 0 ∨ k == n then 1
else comb (n-1) k + comb (n-1) (k-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem llm_heq_of_eq {α} {a b : α} (h : a = b) : HEq a b := by
  cases h
  rfl
-- </vc-helpers>

-- <vc-definitions>
def Comb (n : Nat) (k : Nat) : Nat :=
comb n k
-- </vc-definitions>

-- <vc-theorems>
theorem Comb_spec (n : Nat) (k : Nat) :
0 ≤ k ∧ k ≤ n → Comb n k = comb n k :=
by
  intro _
  rfl
-- </vc-theorems>
