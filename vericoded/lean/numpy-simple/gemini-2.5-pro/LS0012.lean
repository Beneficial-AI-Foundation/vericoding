import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def list_float_sum (l: List Float) : Float := l.foldl (·+·) 0.0

-- </vc-helpers>

-- <vc-definitions>
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float :=
  list_float_sum <| (List.range (n + 1)).map fun k =>
    arr1.getD k 0.0 * arr2.getD (n - k) 0.0

def convolve (arr1 arr2 : List Float) : List Float :=
  if arr1.isEmpty ∨ arr2.isEmpty then
    []
  else
    List.map (convolutionSum arr1 arr2) (List.range (arr1.length + arr2.length - 1))
-- </vc-definitions>

-- <vc-theorems>
theorem convolve_spec (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 :=
by
  unfold convolve
  have h_cond : ¬(arr1.isEmpty ∨ arr2.isEmpty) := by
    rintro (h_empty | h_empty)
    · exact Nat.ne_of_gt h1 (List.isEmpty_iff_length_eq_zero.mp h_empty)
    · exact Nat.ne_of_gt h2 (List.isEmpty_iff_length_eq_zero.mp h_empty)
  rw [if_neg h_cond]
  simp [List.length_map, List.length_range]
-- </vc-theorems>
