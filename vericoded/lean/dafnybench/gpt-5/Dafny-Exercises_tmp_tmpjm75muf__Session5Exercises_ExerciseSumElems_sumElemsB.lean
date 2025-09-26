import Mathlib
-- <vc-preamble>
partial def SumR (s : Array Int) : Int :=
if s.size = 0 then 0
else SumR (s.extract 0 (s.size - 1)) + s[s.size - 1]!
decreasing_by all_goals simp_wf; omega
partial def SumL (s : Array Int) : Int :=
if s.size = 0 then 0
else s[0]! + SumL (s.extract 1 s.size)
decreasing_by all_goals simp_wf; omega
def SumV (v : Array Int) (c : Nat) (f : Nat) : Int :=
SumR (v.extract c f)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem sumV_eq (v : Array Int) (c f : Nat) : SumV v c f = SumR (v.extract c f) := rfl
-- </vc-helpers>

-- <vc-definitions>
def sumElemsB (v : Array Int) : Int :=
SumV v 0 v.size
-- </vc-definitions>

-- <vc-theorems>
theorem sumElemsB_spec (v : Array Int) :
sumElemsB v = SumR (v.extract 0 v.size) :=
rfl
-- </vc-theorems>
