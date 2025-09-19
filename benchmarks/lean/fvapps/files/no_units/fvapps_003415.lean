-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nb (n : Int) : Int := sorry

def sum_cubes (n : Nat) : Nat := sorry

/- For small perfect cubes (n ≤ 10), find_nb correctly returns n when given sum of first n cubes -/
-- </vc-definitions>

-- <vc-theorems>
theorem find_nb_small_perfect_cubes (n : Nat) (h : n ≤ 10) :
  find_nb (sum_cubes n) = n := sorry
-- </vc-theorems>