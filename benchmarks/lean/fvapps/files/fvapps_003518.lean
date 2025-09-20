-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def heron (a b c : Float) : Float := sorry

theorem heron_positive (a b c : Float)
  (h1 : a > 0) (h2 : b > 0) (h3 : c > 0)
  (h4 : a + b > c) (h5 : b + c > a) (h6 : a + c > b) :
  heron a b c > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem heron_matches_formula (a b c : Float)
  (h1 : a > 0) (h2 : b > 0) (h3 : c > 0)
  (h4 : a + b > c) (h5 : b + c > a) (h6 : a + c > b) :
  let s := (a + b + c) / 2
  heron a b c = Float.sqrt (s * (s - a) * (s - b) * (s - c)) := sorry

theorem heron_symmetric (a b c : Float)
  (h1 : a > 0) (h2 : b > 0) (h3 : c > 0)  
  (h4 : a + b > c) (h5 : b + c > a) (h6 : a + c > b) :
  heron a b c = heron a c b ∧ 
  heron a b c = heron b a c := sorry

theorem heron_equilateral (side : Float)
  (h : side > 0) :
  heron side side side = (side * side * Float.sqrt 3) / 4 := sorry
-- </vc-theorems>