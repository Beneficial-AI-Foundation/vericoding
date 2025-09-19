-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfSquares (l : List Int) : Int :=
  sorry

def sumOfCubes (l : List Int) : Int :=
  sorry

def array_madness (a b : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_madness_correct (a b : List Int) (h1 : a.length > 0) (h2 : b.length > 0) :
  array_madness a b = (sumOfSquares a > sumOfCubes b) :=
sorry

theorem small_numbers_property
    (a b : List Int)
    (h1 : a.length > 0)
    (h2 : b.length > 0)
    (ha : ∀ x ∈ a, 0 ≤ x ∧ x ≤ 10)
    (hb : ∀ x ∈ b, 1 ≤ x ∧ x ≤ 10)
    (h : sumOfSquares a ≤ sumOfCubes b) :
  array_madness a b = false :=
sorry
-- </vc-theorems>