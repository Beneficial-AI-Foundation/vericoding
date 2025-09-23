-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def complex_number_multiply : Complex → Complex → Complex
| c1, c2 => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem complex_multiplication_correct (a b : Complex) :
  let result := complex_number_multiply a b
  let expected_real := a.real * b.real - a.imag * b.imag 
  let expected_imag := a.real * b.imag + a.imag * b.real
  result.real = expected_real ∧ result.imag = expected_imag :=
sorry

theorem multiply_by_identity (c : Complex) :
  complex_number_multiply c ⟨1, 0⟩ = c :=
sorry

theorem multiply_by_zero (c : Complex) :
  complex_number_multiply c ⟨0, 0⟩ = ⟨0, 0⟩ :=
sorry

/-
info: '0+2i'
-/
-- #guard_msgs in
-- #eval complex_number_multiply "1+1i" "1+1i"

/-
info: '0+-2i'
-/
-- #guard_msgs in
-- #eval complex_number_multiply "1+-1i" "1+-1i"

/-
info: '23+2i'
-/
-- #guard_msgs in
-- #eval complex_number_multiply "2+3i" "4+-5i"
-- </vc-theorems>