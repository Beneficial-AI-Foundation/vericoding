-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Find (a : Array Int) (key : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Find_spec (a : Array Int) (key : Int) (i : Int) :
i = Find a key →
(0 ≤ i →
(i < a.size ∧
a[i.toNat]! = key ∧
(∀ k, 0 ≤ k ∧ k < i → a[k.toNat]! ≠ key))) ∧
(i < 0 →
(∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≠ key)) :=
sorry
-- </vc-theorems>