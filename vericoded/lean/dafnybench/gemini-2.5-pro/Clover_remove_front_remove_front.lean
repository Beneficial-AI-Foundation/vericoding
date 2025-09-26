import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def remove_front (a : Array Int) : Array Int :=
a.extract 1 a.size
-- </vc-definitions>

-- <vc-theorems>
theorem remove_front_spec (a : Array Int) :
a.size > 0 →
∀ (c : Array Int), remove_front a = c →
c.size = a.size - 1 :=
by
  rintro h_pos c rfl
  simp [remove_front, Array.size_extract, Nat.min_self, h_pos]
-- </vc-theorems>
