-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def waveSort (arr : List Int) : List Int := sorry

def isWaveSorted (arr : List Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem waveSort_preservation (arr : List Int) :
  let result := waveSort arr
  List.length result = List.length arr ∧ 
  result.toArray = arr.toArray ∧ 
  isWaveSorted result := sorry

theorem waveSort_alternating (arr : List Int) :
  arr.length ≥ 2 →
  let result := waveSort arr
  ∀ i, 1 ≤ i → i < result.length → i % 2 = 1 →
    (result[i]! ≤ result[i-1]! ∧
     (i + 1 < result.length → result[i]! ≤ result[i+1]!)) := sorry

theorem waveSort_small_arrays (arr : List Int) :
  arr.length ≤ 1 →
  waveSort arr = arr := sorry
-- </vc-theorems>