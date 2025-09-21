-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsGreater (n : Int) (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsGreater_spec (n : Int) (a : Array Int) :
(IsGreater n a = true → ∀ i, 0 ≤ i ∧ i < a.size → n > a[i]!) ∧
(IsGreater n a = false → ∃ i, 0 ≤ i ∧ i < a.size ∧ n ≤ a[i]!) :=
sorry
-- </vc-theorems>