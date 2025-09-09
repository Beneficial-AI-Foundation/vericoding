-- <vc-helpers>
-- </vc-helpers>

def square_free_part (n : Int) : Option Int := sorry

def Real.toInt (x : Float) : Int := sorry

theorem non_integer_returns_none (x : Float) : 
  square_free_part (Real.toInt x) = none := by sorry

theorem non_positive_returns_none (x : Int) : 
  x ≤ 0 → square_free_part x = none := by sorry

theorem result_divides_input (n : Int) :
  n > 0 → 
  match square_free_part n with
  | some result => result ∣ n 
  | none => True
  := by sorry

theorem no_square_factors (n : Int) :
  n > 0 →
  match square_free_part n with
  | some result => ∀ i : Int, i > 1 → ¬(i * i ∣ result)  
  | none => True
  := by sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval square_free_part 24

/-
info: 1
-/
-- #guard_msgs in
-- #eval square_free_part 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval square_free_part 4

/-
info: 10
-/
-- #guard_msgs in
-- #eval square_free_part 100

-- Apps difficulty: introductory
-- Assurance level: unguarded