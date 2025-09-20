-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_stars (n : Nat) (a b c d : Int) (stars : List (Int × Int)) : Nat := sorry

theorem output_bounds {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0) 
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  let result := find_max_stars n a b c d stars
  result ≥ 0 ∧ result ≤ stars.length := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_points {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0)) 
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  find_max_stars n a b c d stars = find_max_stars n a b c d (stars ++ stars) := by sorry

theorem empty_stars {n : Nat} {a b c d : Int}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c) :
  find_max_stars n a b c d [] = 0 := by sorry
-- </vc-theorems>