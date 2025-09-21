-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Getmini (a : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Getmini_spec (a : Array Int) (mini : Nat) :
a.size > 0 →
(mini = Getmini a) →
(0 ≤ mini ∧ mini < a.size) ∧
(∀ x, 0 ≤ x ∧ x < a.size → a[mini]! ≤ a[x]!) ∧
(∀ x, 0 ≤ x ∧ x < mini → a[mini]! < a[x]!) :=
sorry
-- </vc-theorems>