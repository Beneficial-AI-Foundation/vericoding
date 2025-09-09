-- <vc-helpers>
-- </vc-helpers>

def integrate (coef : Int) (exp : Nat) : String := sorry

theorem integrate_returns_string (coef : Int) (exp : Nat)
  (h : coef ≠ 0) :
  ∃ s : String, integrate coef exp = s := sorry

theorem integrate_result_ends_with_power 
  (coef : Int) (exp : Nat) (h : coef ≠ 0) :
  ∃ (s : String), integrate coef exp = s ∧ 
  s.endsWith s!"x^{exp + 1}" := sorry

theorem integrate_coef_correct_when_divisible
  (coef : Int) (exp : Nat) (h : coef ≠ 0)
  (h2 : coef % (exp + 1) = 0) :
  ∃ s : String,
    integrate coef exp = s ∧
    s.startsWith (toString (coef / (exp + 1))) := sorry

theorem integrate_coef_correct_when_not_divisible
  (coef : Int) (exp : Nat) (h : coef ≠ 0)
  (h2 : coef % (exp + 1) ≠ 0) :
  ∃ s : String,
    integrate coef exp = s ∧ 
    s.startsWith (toString ((coef / (exp + 1)).toNat)) := sorry

/-
info: '1x^3'
-/
-- #guard_msgs in
-- #eval integrate 3 2

/-
info: '2x^6'
-/
-- #guard_msgs in
-- #eval integrate 12 5

/-
info: '30x^3'
-/
-- #guard_msgs in
-- #eval integrate 90 2

-- Apps difficulty: introductory
-- Assurance level: unguarded