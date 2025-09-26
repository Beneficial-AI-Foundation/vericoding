import Mathlib
-- <vc-preamble>
def Count (hi : Nat) (s : Array Int) : Int :=
if hi = 0 then 0
else if s[(hi-1)]! % 2 = 0 then 1 + Count (hi-1) s
else Count (hi-1) s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance instCoeIntNat : Coe Int Nat where
  coe := Int.toNat
-- </vc-helpers>

-- <vc-definitions>
def ComputeCount (CountIndex : Nat) (a : Array Int) (b : Array Int) : Nat :=
Count CountIndex a
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeCount_spec (CountIndex : Nat) (a : Array Int) (b : Array Int) :
(CountIndex = 0 ∨ (a.size = b.size ∧ 1 ≤ CountIndex ∧ CountIndex ≤ a.size)) →
ComputeCount CountIndex a b = Count CountIndex a :=
by
  intro _
  rfl
-- </vc-theorems>
