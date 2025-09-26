import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper function to safely get list element with default
def getAt (l : List Float) (i : Nat) : Float :=
  l.getD i 0.0
-- </vc-helpers>

-- <vc-definitions>
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float :=
-- Sum over indices where arr1[i] * arr2[n-i] contributes to position n
  (List.range (min arr1.length (n + 1))).foldl
    (fun acc i => 
      if n >= i ∧ (n - i) < arr2.length then
        acc + (getAt arr1 i) * (getAt arr2 (n - i))
      else acc) 0.0

def convolve (arr1 arr2 : List Float) : List Float :=
-- Generate convolution result for each valid output position
  List.range (arr1.length + arr2.length - 1) |>.map (convolutionSum arr1 arr2)
-- </vc-definitions>

-- <vc-theorems>
theorem convolve_spec (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 :=
by
  simp [convolve]
-- </vc-theorems>
