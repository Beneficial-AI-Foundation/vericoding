-- <vc-preamble>
def roundIt (x : Float) : Int := sorry

def floor (x : Float) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ceil (x : Float) : Int := sorry

def floatToStr (x : Float) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem round_it_decimals (x : Float) 
  (h₁ : Float.floor x ≠ x)
  (h₂ : String.length (floatToStr (Float.floor (Float.abs x))) < 
        String.length (floatToStr (Float.abs x - Float.floor (Float.abs x)))) :
  roundIt x = ceil x := sorry

theorem round_it_decimals_floor (x : Float)
  (h₁ : Float.floor x ≠ x)
  (h₂ : String.length (floatToStr (Float.floor (Float.abs x))) >
        String.length (floatToStr (Float.abs x - Float.floor (Float.abs x)))) :
  roundIt x = floor x := sorry

theorem round_it_decimals_equal_length (x : Float)
  (h₁ : Float.floor x ≠ x)
  (h₂ : String.length (floatToStr (Float.floor (Float.abs x))) =
        String.length (floatToStr (Float.abs x - Float.floor (Float.abs x)))) :
  roundIt x = if x > 0 then ceil x else floor x := sorry

theorem round_it_integers (n : Int) :
  roundIt (Float.ofInt n) = n := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval round_it 3.45

/-
info: 34
-/
-- #guard_msgs in
-- #eval round_it 34.5

/-
info: 35
-/
-- #guard_msgs in
-- #eval round_it 34.56
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded