-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polynomialize (roots: List Int) : String := sorry 

def isValidPolynomial (s: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polynomial_format 
  (roots: List Int)
  (h1: roots ≠ [])
  (h2: ∀ x ∈ roots, -100 ≤ x ∧ x ≤ 100) :
  isValidPolynomial (polynomialize roots) := sorry

theorem zero_roots
  (zeros: List Int) 
  (h1: zeros.length ≥ 2)
  (h2: zeros.length ≤ 10)
  (h3: ∀ x ∈ zeros, x = 0) :
  polynomialize zeros = s!"x^{zeros.length} = 0" := sorry

/-
info: 'x = 0'
-/
-- #guard_msgs in
-- #eval polynomialize [0]

/-
info: 'x^2 = 0'
-/
-- #guard_msgs in
-- #eval polynomialize [0, 0]

/-
info: 'x^3 + 5x^2 + 6x = 0'
-/
-- #guard_msgs in
-- #eval polynomialize [0, -2, -3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded