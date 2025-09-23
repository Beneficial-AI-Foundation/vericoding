-- <vc-preamble>
def abs (x : Int) : Int := if x < 0 then -x else x

structure VampireString where
  digits : List Char
  length : Nat
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vampireToString (x : Int) : VampireString := sorry

def vampire_test (x y : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vampire_commutative (x y : Int) (h₁ : x ≠ 0) (h₂ : y ≠ 0) :
  vampire_test x y = vampire_test y x := sorry

theorem vampire_self_multiply (x : Int) (h : x ≠ 0) :  
  vampire_test x x = vampire_test x x := sorry

theorem vampire_digit_preservation (x y : Int) (h₁ : x ≠ 0) (h₂ : y ≠ 0) :
  vampire_test x y → (vampireToString (abs (x * y))).digits = 
    (vampireToString (abs x)).digits ++ (vampireToString (abs y)).digits := sorry

theorem vampire_positive_length (x y : Int) (h₁ : x > 0) (h₂ : y > 0) :
  vampire_test x y → (vampireToString (x * y)).length = 
    (vampireToString x).length + (vampireToString y).length := sorry
-- </vc-theorems>