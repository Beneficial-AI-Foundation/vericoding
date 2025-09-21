-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Difference (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem difference_spec (a b diff : Array Int) :
diff = Difference a b →
(∀ x, diff.contains x ↔ (a.contains x ∧ ¬b.contains x)) ∧
(∀ i j, 0 ≤ i → i < j → j < diff.size → diff[i]! ≠ diff[j]!) :=
sorry
-- </vc-theorems>