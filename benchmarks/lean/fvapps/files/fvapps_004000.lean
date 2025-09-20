-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxlen (s1 s2 : Float) : Float := sorry

theorem maxlen_upper_bound (s1 s2 : Float) 
  (h1 : s1 > 0) (h2 : s2 > 0) : 
  maxlen s1 s2 ≤ max s1 s2 / 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxlen_lower_bound (s1 s2 : Float)
  (h1 : s1 > 0) (h2 : s2 > 0) :
  maxlen s1 s2 ≥ max s1 s2 / 3 := sorry

theorem maxlen_positive (s1 s2 : Float)
  (h1 : s1 > 0) (h2 : s2 > 0) :
  maxlen s1 s2 > 0 := sorry

theorem maxlen_symmetric (s1 s2 : Float)
  (h1 : s1 > 0) (h2 : s2 > 0) :
  maxlen s1 s2 = maxlen s2 s1 := sorry

theorem maxlen_equal_inputs (x : Float)
  (h : x > 0) :
  maxlen x x = x / 2 := sorry
-- </vc-theorems>