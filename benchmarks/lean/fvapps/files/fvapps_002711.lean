-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Int) : Int :=
  sorry

def peak (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem peak_equal_sums (arr : List Int) (h_size : arr.length > 0) :
  let p := peak arr;
  p ≠ -1 →
  sum (arr.take (Int.toNat p)) = sum (arr.drop (Int.toNat (p + 1))) :=
sorry

theorem peak_bounds (arr : List Int) :
  let p := peak arr;
  -1 ≤ p ∧ p < arr.length :=
sorry

theorem peak_single_element (arr : List Int) (h : arr.length = 1) :
  peak arr = 0 :=
sorry

theorem peak_empty :
  peak [] = -1 :=
sorry
-- </vc-theorems>