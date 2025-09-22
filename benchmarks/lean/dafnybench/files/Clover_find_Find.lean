-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Find (a : Array Int) (key : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Find_spec (a : Array Int) (key : Int) :
-1 ≤ Find a key ∧ Find a key < a.size ∧
(Find a key ≠ -1 → ∃ idx : Nat, idx < a.size ∧ a[idx]! = key ∧
(∀ i, 0 ≤ i ∧ i < idx → a[i]! ≠ key)) ∧
(Find a key = -1 → (∀ i, 0 ≤ i ∧ i < a.size → a[i]! ≠ key)) :=
sorry
-- </vc-theorems>