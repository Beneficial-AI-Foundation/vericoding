-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def consecutiveSum (arr : List Int) : List String := sorry

theorem length_property (arr : List Int) 
    (h : arr.length ≥ 3) :
    (consecutiveSum arr).length = arr.length - 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_strings (arr : List Int) 
    (h : arr.length ≥ 3) :
    ∀ x ∈ consecutiveSum arr, x.length ≥ 1 := sorry

theorem sum_property (arr : List Int)
    (h : arr.length ≥ 3)
    (i : Nat)
    (hi : i < arr.length - 2) :
    ∀ x ∈ consecutiveSum arr, String.toInt! x = 
      arr[i]! + arr[i+1]! + arr[i+2]! := sorry

theorem monotonic_positive (arr : List Int)
    (h : arr.length ≥ 3)
    (h2 : ∀ x ∈ arr, x ≥ 0)
    (i : Nat)
    (hi : i < arr.length - 2) :
    String.toInt! (consecutiveSum arr)[i]! ≥ 
      min arr[i]! (min arr[i+1]! arr[i+2]!) := sorry

theorem all_zeros (arr : List Int)
    (h : arr.length ≥ 3)
    (h2 : ∀ x ∈ arr, x = 0) :
    ∀ x ∈ consecutiveSum arr, x = "0" := sorry
-- </vc-theorems>