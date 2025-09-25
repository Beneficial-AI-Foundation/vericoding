-- <vc-preamble>
def Count (hi : Nat) (s : Array Int) : Int :=
if hi = 0 then 0
else if s[(hi-1)]! % 2 = 0 then 1 + Count (hi-1) s
else Count (hi-1) s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FooCount (CountIndex : Nat) (a : Array Int) (b : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FooCount_spec (CountIndex : Nat) (a b : Array Int) :
(CountIndex = 0 ∨ (a.size = b.size ∧ 1 ≤ CountIndex ∧ CountIndex ≤ a.size)) →
FooCount CountIndex a b = Count CountIndex a :=
sorry
-- </vc-theorems>