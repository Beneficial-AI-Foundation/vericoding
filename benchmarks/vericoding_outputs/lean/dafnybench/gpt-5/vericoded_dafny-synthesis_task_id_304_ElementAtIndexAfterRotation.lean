import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def rotatedIndex (size i n : Nat) : Nat :=
  (i - n + size) % size

@[simp] theorem rotatedIndex_eq (size i n : Nat) :
  rotatedIndex size i n = (i - n + size) % size := rfl
-- </vc-helpers>

-- <vc-definitions>
def ElementAtIndexAfterRotation (l : Array Int) (n : Nat) (index : Nat) : Int :=
l[((index - n + l.size) % l.size)]!
-- </vc-definitions>

-- <vc-theorems>
theorem ElementAtIndexAfterRotation_spec
(l : Array Int) (n : Nat) (index : Nat) :
n ≥ 0 →
0 ≤ index →
index < l.size →
ElementAtIndexAfterRotation l n index = l[((index - n + l.size) % l.size)]! :=
by
  intro _ _ _
  rfl
-- </vc-theorems>
