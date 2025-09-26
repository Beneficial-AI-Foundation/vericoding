import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def Reverse (a : Array Char) : Array Char :=
Array.ofFn (fun (i : Fin a.size) => a[a.size - (i : Nat) - 1]!)
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_spec (a : Array Char) (b : Array Char) :
a.size > 0 →
b = Reverse a →
(b.size = a.size ∧
∀ i, 0 ≤ i ∧ i < a.size → b[i]! = a[a.size - i - 1]!) :=
by
  intro _ hb
  subst hb
  constructor
  · simp [Reverse]
  · intro i hi
    have hi' : i < a.size := hi.right
    simpa [Reverse, hi']
-- </vc-theorems>
