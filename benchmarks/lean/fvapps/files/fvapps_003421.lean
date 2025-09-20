-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eq_sum_powdig (hmax : Nat) (exp : Nat) : List Nat := sorry

def sum_digit_powers : Nat → Nat → Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eq_sum_powdig_increasing_range {hmax : Nat} (h : hmax ≥ 1) :
  let small_result := eq_sum_powdig hmax 3;
  let large_result := eq_sum_powdig (hmax + 100) 3;
  ∀ x ∈ small_result, x ∈ large_result := sorry

theorem eq_sum_powdig_known_values :
  153 ∈ eq_sum_powdig 153 3 ∧ 370 ∈ eq_sum_powdig 370 3 := sorry
-- </vc-theorems>