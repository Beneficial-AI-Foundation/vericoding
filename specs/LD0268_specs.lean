-- <vc-preamble>
def min_ (a b : Int) : Int :=
if a < b then a else b

def minFunction (a b : Int) : Int :=
if a < b then a else b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minArray (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_spec (a b : Int) :
(min_ a b ≤ a ∧ min_ a b ≤ b) ∧
(min_ a b = a ∨ min_ a b = b) :=
sorry

theorem minFunction_spec (a b : Int) :
(minFunction a b ≤ a ∧ minFunction a b ≤ b) ∧
(minFunction a b = a ∨ minFunction a b = b) :=
sorry

theorem minArray_spec (a : Array Int) :
a.size > 0 →
(∀ k : Nat, k < a.size → minArray a ≤ a[k]!) ∧
(∃ k : Nat, k < a.size ∧ minArray a = a[k]!) :=
sorry
-- </vc-theorems>