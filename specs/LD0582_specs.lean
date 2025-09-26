-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Filter (a : Array Char) (b : List Char) : List Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Filter_spec (a : Array Char) (b : List Char) (c : List Char) :
c = Filter a b →
(∀ x, (x ∈ a.toList ∧ x ∈ b) ↔ x ∈ c) :=
sorry
-- </vc-theorems>