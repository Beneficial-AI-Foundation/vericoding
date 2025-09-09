-- <vc-helpers>
-- </vc-helpers>

def is_valid_triangle (a b c : Int) : String :=
  sorry

theorem is_valid_triangle_output_valid (a b c : Int) :
  is_valid_triangle a b c = "YES" ∨ is_valid_triangle a b c = "NO" :=
  sorry

theorem valid_triangle_angle_properties {a b c : Int} :
  is_valid_triangle a b c = "YES" →
  a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 180 :=
  sorry

theorem valid_triangle_construction (a b : Int) 
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 178) (h4 : b ≤ 178) :
  let c := 180 - a - b
  if c > 0 then
    is_valid_triangle a b c = "YES"
  else 
    is_valid_triangle a b c = "NO" :=
  sorry

theorem negative_or_zero_angles (x : Int) (h : x ≤ 0) :
  is_valid_triangle x 90 90 = "NO" ∧
  is_valid_triangle 90 x 90 = "NO" ∧
  is_valid_triangle 90 90 x = "NO" :=
  sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval is_valid_triangle 40 40 100

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval is_valid_triangle 45 45 90

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval is_valid_triangle 180 1 1

-- Apps difficulty: interview
-- Assurance level: unguarded