import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def getWithDefault (lst : List Float) (idx : Nat) : Float :=
  if h : idx < lst.length then
    lst.get ⟨idx, h⟩
  else
    0.0
-- </vc-helpers>

-- <vc-definitions>
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float :=
let len1 := arr1.length
  let len2 := arr2.length
  if n < len1 + len2 - 1 then
    let indices := List.range (n + 1)
    indices.foldl (fun acc i =>
      let j := n - i
      if i < len1 ∧ j < len2 then
        acc + getWithDefault arr1 i * getWithDefault arr2 j
      else
        acc) 0.0
  else
    0.0

def convolve (arr1 arr2 : List Float) : List Float :=
if arr1.isEmpty || arr2.isEmpty then
    []
  else
    let resultLen := arr1.length + arr2.length - 1
    List.range resultLen |>.map (convolutionSum arr1 arr2)
-- </vc-definitions>

-- <vc-theorems>
theorem convolve_spec (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 :=
by
  simp [convolve]
  have not_empty1 : ¬arr1.isEmpty := by
    simp [List.isEmpty_iff]
    intro h
    rw [h, List.length_nil] at h1
    simp at h1
  have not_empty2 : ¬arr2.isEmpty := by
    simp [List.isEmpty_iff]
    intro h
    rw [h, List.length_nil] at h2
    simp at h2
  simp [not_empty1, not_empty2, List.length_map, List.length_range]
-- </vc-theorems>
