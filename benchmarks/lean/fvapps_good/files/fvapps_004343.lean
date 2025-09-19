-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def invert (xs : List Int) : List Int := sorry

def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-definitions>

-- <vc-theorems>
theorem invert_length (xs : List Int) :
  (invert xs).length = xs.length := sorry

theorem invert_involution (xs : List Int) :
  invert (invert xs) = xs := sorry

theorem invert_empty : 
  invert [] = [] := sorry
-- </vc-theorems>