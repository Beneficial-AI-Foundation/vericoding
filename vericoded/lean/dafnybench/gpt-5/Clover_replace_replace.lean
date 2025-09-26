import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed.

-- </vc-helpers>

-- <vc-definitions>
def replace (arr : Array Int) (k : Int) : Array Int :=
arr.map (fun x => if x > k then (-1) else x)
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec (arr : Array Int) (k : Int) (i : Nat) :
i < arr.size →
let result := replace arr k
(arr[i]! > k → result[i]! = -1) ∧
(arr[i]! ≤ k → result[i]! = arr[i]!) :=
by
  intro hi
  simpa [replace] using
    (show
      (arr[i]! > k → (replace arr k)[i]! = -1) ∧
      (arr[i]! ≤ k → (replace arr k)[i]! = arr[i]!)
      from
      by
        have hres :
            (replace arr k)[i]! = (if arr[i]! > k then -1 else arr[i]!) := by
          simpa [replace, hi]
        constructor
        · intro hgt
          simpa [hres, hgt]
        · intro hle
          simpa [hres, not_lt.mpr hle])
-- </vc-theorems>
