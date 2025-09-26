import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemmas for square root
lemma sqrt_aux_spec (n k : Nat) : k * k ≤ n → n < (k + 1) * (k + 1) → 
  (∀ m, m * m ≤ n → m ≤ k) := by
  intros h1 h2 m hm
  by_contra h
  have : k + 1 ≤ m := Nat.lt_iff_add_one_le.mp (Nat.not_le.mp h)
  have : (k + 1) * (k + 1) ≤ m * m := Nat.mul_self_le_mul_self this
  have : n < m * m := lt_of_lt_of_le h2 this
  exact Nat.not_le.mpr this hm
-- </vc-helpers>

-- <vc-definitions>
def SquareRoot (N : Nat) : Nat :=
-- Use Nat.sqrt from Mathlib
Nat.sqrt N
-- </vc-definitions>

-- <vc-theorems>
theorem SquareRoot_spec (N : Nat) :
let r := SquareRoot N
r * r ≤ N ∧ N < (r + 1) * (r + 1) :=
-- Use the existing Nat.sqrt lemmas from Mathlib
⟨Nat.sqrt_le N, Nat.lt_succ_sqrt N⟩
-- </vc-theorems>
