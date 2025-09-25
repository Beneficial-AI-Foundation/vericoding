-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greatest_product (s : String) : Nat := sorry

def digit_product (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_gives_zero_window {s : String} (h : s.length ≥ 5) :
  let with_zero := s.take 3 ++ "0" ++ s.drop 3
  if with_zero.contains '0' then
    greatest_product with_zero = 0 ∨ ∃ d, d ∈ with_zero.data ∧ d.toNat > 0
  else True := sorry
-- </vc-theorems>