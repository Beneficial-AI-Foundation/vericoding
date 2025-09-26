import Mathlib
-- <vc-preamble>
def positive (s : Array Int) : Prop :=
∀ u, 0 ≤ u ∧ u < s.size → s[u]! ≥ 0
def isEven (i : Int) : Bool :=
i ≥ 0 → i % 2 = 0
partial def CountEven (s : Array Int) : Int :=
if s.size = 0 then 0
else
let last := s[s.size - 1]!
let rest := s.extract 0 (s.size - 1)
(if last % 2 = 0 then 1 else 0) + CountEven rest
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed for this development
-- </vc-helpers>

-- <vc-definitions>
def mcountEven (v : Array Int) : Int :=
CountEven v
-- </vc-definitions>

-- <vc-theorems>
theorem mcountEven_spec (v : Array Int) :
positive v → mcountEven v = CountEven v :=
fun _ => rfl
-- </vc-theorems>
