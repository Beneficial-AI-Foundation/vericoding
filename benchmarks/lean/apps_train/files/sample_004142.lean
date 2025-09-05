There exist two zeroes: +0 (or just 0) and -0.

Write a function that returns `true` if the input number is -0 and `false` otherwise (`True` and `False` for Python).

In JavaScript / TypeScript / Coffeescript the input will be a number.

In Python / Java / C / NASM / Haskell / the input will be a float.

def is_negative_zero (x : Float) : Bool := sorry

/-- Helper function to emulate sign behavior -/

def getSign (x : Float) : Float := sorry

theorem is_negative_zero_main (x : Float) :
  is_negative_zero x = true ↔ (getSign x < 0 ∧ x = 0) := sorry

def posInf : Float := sorry
def negInf : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded