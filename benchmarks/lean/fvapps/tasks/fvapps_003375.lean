-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chromosome_check (sperm : String) : String := sorry

theorem chromosome_check_XY :
  (chromosome_check "XY").contains 's' ∧ 
  (chromosome_check "XY").contains 'o' ∧ 
  (chromosome_check "XY").contains 'n' :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chromosome_check_XX :
  (chromosome_check "XX").contains 'd' ∧ 
  (chromosome_check "XX").contains 'a' ∧ 
  (chromosome_check "XX").contains 'u' ∧
  (chromosome_check "XX").contains 'g' ∧ 
  (chromosome_check "XX").contains 'h' ∧ 
  (chromosome_check "XX").contains 't' ∧
  (chromosome_check "XX").contains 'e' ∧ 
  (chromosome_check "XX").contains 'r' :=
sorry
-- </vc-theorems>