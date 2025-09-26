import Mathlib
-- <vc-preamble>
partial def sumTo (a : Array Int) (start : Nat) (end_ : Nat) : Int :=
if start == end_ then
0
else
sumTo a start (end_ - 1) + a[end_ - 1]!
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def SumInRange (a : Array Int) (start : Nat) (end_ : Nat) : Int :=
if h : start ≤ end_ ∧ end_ ≤ a.size then
  sumTo a start end_
else
  0
-- </vc-definitions>

-- <vc-theorems>
theorem SumInRange_spec (a : Array Int) (start : Nat) (end_ : Nat) :
start ≥ 0 ∧ start ≤ end_ ∧ end_ ≤ a.size →
SumInRange a start end_ = sumTo a start end_ :=
by
  intro h
  simpa [SumInRange, And.right h]
-- </vc-theorems>
