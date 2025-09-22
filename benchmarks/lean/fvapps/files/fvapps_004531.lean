-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Int.toFloat : Int → Float := sorry

def clean_mean (xs : List Int) (k : Float) : Float := sorry

-- For identical values, clean mean should equal the value
-- </vc-definitions>

-- <vc-theorems>
theorem clean_mean_identical_values {x : Int} {n : Nat} :
  n ≥ 2 → clean_mean (List.replicate n x) 2.0 = Int.toFloat x := sorry

-- Test with known outcomes

theorem clean_mean_basic_test1 :
  clean_mean [1, 2, 3, 4, 5] 2.0 = 3.0 := sorry

theorem clean_mean_basic_test2 :
  clean_mean [1, 2, 3, 4, 5, 100] 2.0 = 3.0 := sorry

theorem clean_mean_basic_test3 :
  clean_mean [1, 1, 2, 2, 3, 3] 2.0 = 2.0 := sorry
-- </vc-theorems>