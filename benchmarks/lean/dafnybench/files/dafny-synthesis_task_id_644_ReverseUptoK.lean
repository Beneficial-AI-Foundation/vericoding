-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ReverseUptoK (s : Array Int) (k : Nat) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ReverseUptoK_spec (s : Array Int) (k : Nat) (old_s : Array Int) :
2 ≤ k ∧ k ≤ s.size →
(∀ i, 0 ≤ i ∧ i < k → (ReverseUptoK s k)[i]! = old_s[k - 1 - i]!) ∧
(∀ i, k ≤ i ∧ i < s.size → (ReverseUptoK s k)[i]! = old_s[i]!) :=
sorry
-- </vc-theorems>