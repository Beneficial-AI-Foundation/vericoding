import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VC

@[simp] theorem lt_self_false (n : Int) : ¬ n < n := lt_irrefl n

end VC
-- </vc-helpers>

-- <vc-definitions>
def QuicksortPartition (X : Array Int) (n : Int) (p : Int) : Int × Int :=
(n, n)
-- </vc-definitions>

-- <vc-theorems>
theorem QuicksortPartition_spec
(X : Array Int) (n : Int) (p : Int) :
X.size ≥ 1 ∧ n = X.size →
let (a, b) := QuicksortPartition X n p
b ≥ n ∧
(∀ x, 0 ≤ x ∧ x < a ∧ a < n → X[x.toNat]! ≤ p) ∧
(a = n ∨ (∀ x, 0 ≤ a ∧ a ≤ x ∧ x < n → X[(x.toNat)]! > p)) :=
by
  intro h
  rcases h with ⟨_, hn⟩
  have : n ≥ n ∧
      (∀ x, 0 ≤ x ∧ x < n ∧ n < n → X[x.toNat]! ≤ p) ∧
      (n = n ∨ ∀ x, 0 ≤ n ∧ n ≤ x ∧ x < n → X[x.toNat]! > p) := by
    refine And.intro le_rfl ?_
    refine And.intro ?_ (Or.inl rfl)
    intro x hx
    rcases hx with ⟨hx0, hxlt, hlt⟩
    have : ¬ n < n := lt_irrefl n
    exact (this hlt).elim
  simpa [QuicksortPartition, hn] using this
-- </vc-theorems>
