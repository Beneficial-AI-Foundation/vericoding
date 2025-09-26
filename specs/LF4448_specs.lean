-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits_product (n : Nat) : Int := sorry

def stringToDigitProduct (s : String) : Nat :=
  s.toList.map (fun c => c.toNat - 48)
    |>.foldl (· * ·) 1
-- </vc-definitions>

-- <vc-theorems>
theorem digits_product_result_range (n : Nat) :
  let result := digits_product n
  result = -1 ∨ result > 0 := by sorry

theorem digits_product_single_digit (n : Nat) (h : n ≤ 9) :
  digits_product n = (if n = 0 then 10 else 10 + n) := by sorry

theorem digits_product_product_matches (n : Nat) :
  let result := digits_product n
  result ≠ -1 →
  stringToDigitProduct (toString result.toNat) = n := by sorry
-- </vc-theorems>