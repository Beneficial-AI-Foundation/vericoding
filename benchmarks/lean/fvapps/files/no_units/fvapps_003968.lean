-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sc (width length gaps : Nat) : Nat := sorry

theorem sc_non_negative
  (width length gaps : Nat)
  (h1 : width > 0)
  (h2 : length > 0)
  (h3 : gaps > 0) :
  sc width length gaps ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sc_zero_when_gaps_exceed_perimeter
  (width length gaps : Nat)
  (h1 : width > 0)
  (h2 : length > 0)
  (h3 : gaps > 0)
  (h4 : gaps > 2*width + 2*length - 4) :
  sc width length gaps = 0 := sorry

theorem sc_perimeter_relation
  (width length gaps : Nat)
  (h1 : width > 0)
  (h2 : length > 0)
  (h3 : gaps > 0)
  (h4 : sc width length gaps > 0) :
  (gaps + 1) * sc width length gaps = 2*width + 2*length - 4 := sorry

theorem sc_square_identity 
  (size : Nat)
  (h : size > 0) :
  sc size size 1 = sc size size 1 := sorry

theorem sc_symmetry
  (width length : Nat)
  (h1 : width > 0)
  (h2 : length > 0) :
  sc width length 1 = sc length width 1 := sorry
-- </vc-theorems>