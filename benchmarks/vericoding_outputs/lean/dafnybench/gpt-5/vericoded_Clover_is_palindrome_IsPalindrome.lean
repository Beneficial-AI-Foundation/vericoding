import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma decide_eq_true_iff' (p : Prop) [Decidable p] : decide p = true ↔ p := by
  by_cases hp : p <;> simp [hp]

-- LLM HELPER
lemma forall_lt_iff_forall_nonneg_and_lt {n : Nat} {P : Nat → Prop} :
  (∀ i, i < n → P i) ↔ (∀ i, 0 ≤ i ∧ i < n → P i) := by
  constructor
  · intro h i hi
    exact h i hi.right
  · intro h i hi
    have h0 : 0 ≤ i := Nat.zero_le i
    exact h i ⟨h0, hi⟩
-- </vc-helpers>

-- <vc-definitions>
def IsPalindrome (x : Array Char) : Bool :=
decide (∀ i, i < x.size → x[i]! = x[x.size - i - 1]!)
-- </vc-definitions>

-- <vc-theorems>
theorem IsPalindrome_spec (x : Array Char) :
IsPalindrome x = true ↔
(∀ i, 0 ≤ i ∧ i < x.size → x[i]! = x[x.size - i - 1]!) :=
by
  classical
  have h₁ :
      IsPalindrome x = true ↔
        (∀ i, i < x.size → x[i]! = x[x.size - i - 1]!) := by
    unfold IsPalindrome
    simpa using
      (decide_eq_true_iff' (p := ∀ i, i < x.size → x[i]! = x[x.size - i - 1]!))
  have h₂ :
      (∀ i, i < x.size → x[i]! = x[x.size - i - 1]!) ↔
        (∀ i, 0 ≤ i ∧ i < x.size → x[i]! = x[x.size - i - 1]!) :=
    (forall_lt_iff_forall_nonneg_and_lt (n := x.size)
      (P := fun i => x[i]! = x[x.size - i - 1]!))
  exact h₁.trans h₂
-- </vc-theorems>
