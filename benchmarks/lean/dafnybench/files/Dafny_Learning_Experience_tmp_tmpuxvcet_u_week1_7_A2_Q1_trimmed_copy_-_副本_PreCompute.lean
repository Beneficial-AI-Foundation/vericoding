-- <vc-preamble>
def Count (hi : Nat) (s : Array Int) : Int :=
if hi = 0 then 0
else if s[(hi-1)]! % 2 = 0 then 1 + Count (hi-1) s
else Count (hi-1) s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ComputeCount (CountIndex : Nat) (a : Array Int) (b : Array Int) : Nat :=
sorry

def PreCompute (a b : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Count_spec (hi : Nat) (s : Array Int) :
0 ≤ hi ∧ hi ≤ s.size → Count hi s ≥ 0 :=
sorry

theorem ComputeCount_spec (CountIndex : Nat) (a b : Array Int) :
(CountIndex = 0 ∨ (a.size = b.size ∧ 1 ≤ CountIndex ∧ CountIndex ≤ a.size)) →
ComputeCount CountIndex a b = Count CountIndex a :=
sorry

theorem PreCompute_spec (a b : Array Int) :
a.size = b.size →
(b.size = 0 ∨ (a.size = b.size ∧ 1 ≤ b.size ∧ b.size ≤ a.size)) ∧
∀ p, p = Count b.size a → p = Count b.size a :=
sorry
-- </vc-theorems>