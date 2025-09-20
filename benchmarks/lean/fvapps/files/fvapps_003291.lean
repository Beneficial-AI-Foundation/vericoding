-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def integrate (coef : Int) (exp : Nat) : String := sorry

theorem integrate_returns_string (coef : Int) (exp : Nat)
  (h : coef ≠ 0) :
  ∃ s : String, integrate coef exp = s := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>