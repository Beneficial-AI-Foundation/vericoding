-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_for_factor (base factor : Nat) : Bool := sorry

theorem check_for_factor_multiplies_back {base factor : Nat} (h : check_for_factor base factor = true) (h2 : factor > 0) :
  (base / factor) * factor = base := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_for_factor_has_remainder {base factor : Nat} (h : check_for_factor base factor = false) (h2 : factor > 0) :
  base % factor ≠ 0 := sorry

theorem one_always_factor {base : Nat} :
  check_for_factor base 1 = true := sorry

theorem self_is_factor {base : Nat} (h : base > 0) :
  check_for_factor base base = true := sorry
-- </vc-theorems>