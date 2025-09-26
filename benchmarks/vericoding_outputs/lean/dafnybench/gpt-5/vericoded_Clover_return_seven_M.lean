import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma int_seven_eq : (7 : Int) = 7 := rfl
-- </vc-helpers>

-- <vc-definitions>
def M (x : Int) : Int :=
7
-- </vc-definitions>

-- <vc-theorems>
theorem M_spec (x : Int) : M x = 7 :=
rfl
-- </vc-theorems>
