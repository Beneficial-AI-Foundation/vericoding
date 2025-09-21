-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_front (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_front_spec (a : Array Int) :
a.size > 0 →
∀ (c : Array Int), remove_front a = c →
c.size = a.size - 1 :=
sorry
-- </vc-theorems>