-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_rational_equal (s1 s2 : String) : Bool := sorry

def make_rational_str (n d : Int) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equivalent_fractions
  {n1 d1 n2 d2 : Int}
  (h1 : d1 > 0)
  (h2 : d2 > 0) 
  (h3 : n1 ≥ -1000)
  (h4 : n1 ≤ 1000)
  (h5 : d1 ≤ 100)
  (h6 : n2 ≥ -1000)
  (h7 : n2 ≤ 1000)
  (h8 : d2 ≤ 100)
  (h9 : n1 / d1 = n2 / d2) :
  is_rational_equal (make_rational_str n1 d1) (make_rational_str n2 d2) = true :=
sorry

theorem repeating_nines
  (n : Nat)
  (h1 : n > 0)
  (h2 : n ≤ 9) :
  let s1 := ("0." ++ String.mk (List.replicate n '9') ++ "(9)")
  let s2 := "1."
  is_rational_equal s1 s2 = true :=
sorry
-- </vc-theorems>