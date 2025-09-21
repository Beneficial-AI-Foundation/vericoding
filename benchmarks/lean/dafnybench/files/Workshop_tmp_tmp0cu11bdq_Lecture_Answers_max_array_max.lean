-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spec (a : Array Int) :

-- First ensures clause: max is larger than anything in array

(∀ j:Nat, 0 ≤ j ∧ j < a.size → max a ≥ a[j]!) ∧

-- Second ensures clause: if array non-empty, max exists in array

(a.size > 0 → ∃ j, 0 ≤ j ∧ j < a.size ∧ max a = a[j]!) :=
sorry
-- </vc-theorems>