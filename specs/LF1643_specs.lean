-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rectangle_rotation (a b : Nat) : Nat := sorry

theorem always_positive
  (a b : Nat)
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : a ≤ 1000)
  (h4 : b ≤ 1000) :
  rectangle_rotation a b > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetry
  (a b : Nat)
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : a ≤ 1000)
  (h4 : b ≤ 1000) :
  rectangle_rotation a b = rectangle_rotation b a := sorry
-- </vc-theorems>