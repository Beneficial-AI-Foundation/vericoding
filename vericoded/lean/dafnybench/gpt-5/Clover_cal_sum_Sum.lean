import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def Sum_ (N : Int) : Int :=
if h : 0 ≤ N then N * (N + 1) / 2 else 0
-- </vc-definitions>

-- <vc-theorems>
theorem Sum_spec (N : Int) :
N ≥ 0 → Sum_ N = N * (N + 1) / 2 :=
by
  intro h
  simp [Sum_, h]
-- </vc-theorems>
