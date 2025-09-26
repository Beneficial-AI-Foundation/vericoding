import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Trivial helper lemma about Array.push (kept for expansion). -/
lemma push_eq_self (a : Array Int) (b : Int) : a.push b = a.push b := rfl

-- </vc-helpers>

-- <vc-definitions>
def append (a : Array Int) (b : Int) : Array Int :=
a.push b
-- </vc-definitions>

-- <vc-theorems>
theorem append_spec (a : Array Int) (b : Int) :
append a b = a.push b :=
rfl
-- </vc-theorems>
