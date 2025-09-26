import Mathlib
-- <vc-preamble>
partial def SumR (s : Array Int) : Int :=
if s.size = 0 then 0
else SumR (s.extract 0 (s.size - 1)) + s[s.size - 1]!

partial def SumL (s : Array Int) : Int :=
if s.size = 0 then 0
else s[0]! + SumL (s.extract 1 s.size)

def SumV (v : Array Int) (c : Nat) (f : Nat) : Int :=
SumR (v.extract c f)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem SumV_def (v : Array Int) (c f : Nat) :
  SumV v c f = SumR (v.extract c f) := rfl
-- </vc-helpers>

-- <vc-definitions>
def sumElems (v : Array Int) : Int :=
SumR v
-- </vc-definitions>

-- <vc-theorems>
theorem SumV_spec (v : Array Int) (c f : Nat) :
0 ≤ c ∧ c ≤ f ∧ f ≤ v.size →
SumV v c f = SumR (v.extract c f) :=
by
  intro _
  rfl

theorem sumElems_spec (v : Array Int) :
sumElems v = SumR v :=
rfl
-- </vc-theorems>
