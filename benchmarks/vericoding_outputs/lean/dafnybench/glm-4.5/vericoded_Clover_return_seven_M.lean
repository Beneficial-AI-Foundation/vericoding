import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper utilities for constant functions
def constantFunction {α β : Type} (b : β) (a : α) : β := b
-- </vc-helpers>

-- <vc-definitions>
def M (x : Int) : Int :=
7
-- </vc-definitions>

-- <vc-theorems>
theorem M_spec (x : Int) : M x = 7 :=
rfl
-- </vc-theorems>
