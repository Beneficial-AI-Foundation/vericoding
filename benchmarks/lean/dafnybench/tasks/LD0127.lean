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
-- </vc-helpers>

-- <vc-definitions>
def sumElems (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SumV_spec (v : Array Int) (c f : Nat) :
0 ≤ c ∧ c ≤ f ∧ f ≤ v.size →
SumV v c f = SumR (v.extract c f) :=
sorry

theorem sumElems_spec (v : Array Int) :
sumElems v = SumR v :=
sorry
-- </vc-theorems>