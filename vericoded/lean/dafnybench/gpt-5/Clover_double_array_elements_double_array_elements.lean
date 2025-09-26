import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper code needed.
-- </vc-helpers>

-- <vc-definitions>
def double_array_elements (s : Array Int) : Array Int :=
Array.ofFn (fun i : Fin s.size => 2 * s[i.1]!)
-- </vc-definitions>

-- <vc-theorems>
theorem double_array_elements_spec (s : Array Int) :
∀ i, 0 ≤ i ∧ i < s.size →
(double_array_elements s)[i]! = 2 * s[i]! :=
by
  intro i hi
  have hlt : i < s.size := hi.2
  simpa [double_array_elements, hlt]
-- </vc-theorems>
