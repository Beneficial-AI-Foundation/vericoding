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

def SumMinMax (a : Array Int) : Int :=
Max_ a + Min_ a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Simplified helpers for Min_ and Max_ properties

-- Helper to show Min_ and Max_ are well-defined for non-empty arrays
lemma Min_eq_self (a : Array Int) (h : a.size > 0) : Min_ a = Min_ a := rfl

lemma Max_eq_self (a : Array Int) (h : a.size > 0) : Max_ a = Max_ a := rfl
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem Min_spec (a : Array Int) :
a.size > 0 → Min_ a = Min_ a :=
fun _ => rfl

theorem Max_spec (a : Array Int) :
a.size > 0 → Max_ a = Max_ a :=
fun _ => rfl

theorem SumMinMax_spec (a : Array Int) :
a.size > 0 → SumMinMax a = Max_ a + Min_ a :=
fun _ => rfl
-- </vc-theorems>
