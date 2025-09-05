A triangle is called an equable triangle if its area equals its perimeter. Return `true`, if it is an equable triangle, else return `false`. You will be provided with the length of sides of the triangle. Happy Coding!

def isValidTriangle (a b c : Float) : Prop :=
  (a + b > c) ∧ (b + c > a) ∧ (a + c > b)

def calculateArea (a b c : Float) : Float :=
  let s := (a + b + c) / 2
  Float.sqrt (s * (s - a) * (s - b) * (s - c))

def equableTriangle (a b c : Float) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
