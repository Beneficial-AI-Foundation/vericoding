-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform_triple (p q r a b c : Int) : Int := sorry

theorem identity_transform_is_zero (x y z : Int) : 
  transform_triple x y z x y z = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_differences_sum 
  (p q r a b c : Nat) :
  let result := transform_triple p q r a b c
  (result ≠ -1) →
  result = (max 0 (a - p) + max 0 (b - q) + max 0 (c - r)) := sorry
-- </vc-theorems>