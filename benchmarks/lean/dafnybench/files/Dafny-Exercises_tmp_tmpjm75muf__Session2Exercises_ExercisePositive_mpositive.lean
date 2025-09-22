-- <vc-preamble>
def positive (s : Array Int) : Prop :=
∀ u, 0 ≤ u ∧ u < s.size → s[u]! ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mpositive (v : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mpositive_spec (v : Array Int) :
mpositive v = positive v :=
sorry
-- </vc-theorems>