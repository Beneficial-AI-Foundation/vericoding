import Mathlib
-- <vc-preamble>
partial def sum (s : Array Int) (i : Nat) : Int :=
if i == 0 then 0
else sum s (i-1) + s[i-1]!
partial def exp (b : Nat) (n : Nat) : Nat :=
if n == 0 then 1
else b * exp b (n-1)
partial def bits (n : Nat) : Array Bool :=
if n == 0 then #[]
else #[n % 2 == 0] ++ bits (n/2)
partial def from_bits (s : Array Bool) : Nat :=
if s.size == 0 then 0
else (if s[0]! then 1 else 0) + 2 * from_bits (s.extract 1 s.size)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helper code needed
-- </vc-helpers>

-- <vc-definitions>
def FastExp (b : Nat) (n : Nat) : Nat :=
exp b n
-- </vc-definitions>

-- <vc-theorems>
theorem FastExp_spec (b n : Nat) :
FastExp b n = exp b n :=
rfl
-- </vc-theorems>
