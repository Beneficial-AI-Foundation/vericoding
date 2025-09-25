-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : Int := sorry

theorem solve_type (arr : List Int) (h: arr.length ≥ 3 ∧ arr.length ≤ 20) : 
  solve arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_shift_invariant (arr : List Int) (shift : Int)
    (h: arr.length ≥ 3 ∧ arr.length ≤ 20) :
  solve arr = solve (arr.map (· + shift)) := sorry

theorem solve_scale_invariant (arr : List Int) (scale : Int)
    (h: arr.length ≥ 3 ∧ arr.length ≤ 20) (h2: scale ≠ 0) :
  solve arr = solve (arr.map (· * scale)) := sorry
-- </vc-theorems>