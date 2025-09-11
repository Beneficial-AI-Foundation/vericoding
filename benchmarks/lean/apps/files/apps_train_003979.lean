-- <vc-preamble>
def simplify (n : Nat) : String := sorry
def desimplify (s : String) : Nat := sorry

def containsSqrt (s : String) : Bool := sorry
def countSqrt (s : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isNumeric (s : String) : Bool := sorry
def splitByWhitespace (s : String) : List String := sorry

/- Desimplifying a simplified number returns the original number -/
-- </vc-definitions>

-- <vc-theorems>
theorem simplify_desimplify_roundtrip (n : Nat) (h : n > 0) :
  desimplify (simplify n) = n := sorry

/- A simplified expression contains at most one sqrt -/

theorem simplify_sqrt_count (n : Nat) (h : n > 0) :
  countSqrt (simplify n) ≤ 1 := sorry

/- A simplified expression with no sqrt is a single number -/

theorem simplify_no_sqrt (n : Nat) (h : n > 0) :
  ¬containsSqrt (simplify n) → isNumeric (simplify n).trim := sorry

/- A simplified expression with sqrt is in format "a sqrt b" or "sqrt b" -/

theorem simplify_with_sqrt (n : Nat) (h : n > 0) :
  let s := simplify n
  let parts := splitByWhitespace s
  containsSqrt s →
    (parts.length = 2 ∧ parts.get! 0 = "sqrt" ∧ isNumeric (parts.get! 1)) ∨
    (parts.length = 3 ∧ isNumeric (parts.get! 0) ∧ parts.get! 1 = "sqrt" ∧ isNumeric (parts.get! 2)) := sorry

/- Desimplifying returns a positive integer -/

theorem desimplify_range (n : Nat) (h : n > 0) :
  desimplify (simplify n) > 0 := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval simplify 1

/-
info: '2 sqrt 2'
-/
-- #guard_msgs in
-- #eval simplify 8

/-
info: '2 sqrt 5'
-/
-- #guard_msgs in
-- #eval simplify 20

/-
info: 1
-/
-- #guard_msgs in
-- #eval desimplify "1"

/-
info: 8
-/
-- #guard_msgs in
-- #eval desimplify "2 sqrt 2"

/-
info: 20
-/
-- #guard_msgs in
-- #eval desimplify "2 sqrt 5"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded