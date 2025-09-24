-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def basereduct (n : Nat) : Int := sorry

theorem basereduct_properties {n : Nat} (h : n > 0) :
  let result : Int := basereduct n
  (result ≥ -1 ∧ result ≤ 9) ∧
  (n < 10 → result = n) ∧
  (result ≠ -1 → result ≥ 0 ∧ result ≤ 9)
  := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basereduct_two_digits {n : Nat} (h1 : n ≥ 10) (h2 : n ≤ 100) :
  basereduct n > -1 := by sorry
-- </vc-theorems>