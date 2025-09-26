-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convolutionSum (arr1 arr2 : List Float) (n : Nat) : Float :=
sorry

def convolve (arr1 arr2 : List Float) : List Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convolve_spec (arr1 arr2 : List Float)
  (h1 : arr1.length > 0)
  (h2 : arr2.length > 0) :
  let result := convolve arr1 arr2
  result.length = arr1.length + arr2.length - 1 :=
sorry
-- </vc-theorems>