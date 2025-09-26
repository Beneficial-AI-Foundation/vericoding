import Mathlib
-- <vc-preamble>
partial def Min_ (a : Array Int) : Int :=
if a.size = 1 then
a[0]!
else
let minPrefix := Min_ (a.extract 0 (a.size - 1))
if a[a.size - 1]! ≤ minPrefix then
a[a.size - 1]!
else
Min_ (a.extract 0 (a.size - 1))

partial def Max_ (a : Array Int) : Int :=
if a.size = 1 then
a[0]!
else
let maxPrefix := Max_ (a.extract 0 (a.size - 1))
if a[a.size - 1]! ≥ maxPrefix then
a[a.size - 1]!
else
Max_ (a.extract 0 (a.size - 1))

def DifferenceMinMax (a : Array Int) : Int :=
Max_ a - Min_ a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas for reasoning about Min_ and Max_
-- Note: These partial functions are defined recursively on array extraction
-- The main theorem follows directly from the definition
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem DifferenceMinMax_spec (a : Array Int) :
a.size > 0 →
DifferenceMinMax a = Max_ a - Min_ a :=
fun h => rfl
-- </vc-theorems>
