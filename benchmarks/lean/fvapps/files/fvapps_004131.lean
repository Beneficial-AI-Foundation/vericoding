-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def colorful (n : Nat) : Bool := sorry

def getSubsequenceProducts (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_colorful (n : Nat) (h : n ≤ 9) : 
  colorful n = true := sorry

theorem zero_digit_not_colorful (n : Nat) (h : n ≥ 10) (h2 : ∃ d ∈ getSubsequenceProducts n, d = 0) :
  colorful n = false := sorry

theorem colorful_iff_unique_products (n : Nat) (h : n > 0) (h2 : n < 10000) :
  colorful n = (getSubsequenceProducts n).Nodup := sorry

theorem repeated_digits_not_colorful (n : Nat) (h : n > 0) (h2 : n < 10000)
  (h3 : (toString n).data.length > ((toString n).data.eraseDups).length) :
  colorful n = false := sorry
-- </vc-theorems>