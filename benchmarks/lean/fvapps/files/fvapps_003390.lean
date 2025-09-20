-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dragon_curve (n : α) : String := sorry

theorem dragon_curve_integer_bounds {n : Int} :
  let result := dragon_curve n
  result.all (fun c => c = 'F' ∨ c = 'R' ∨ c = 'L') ∧
  (n < 0 → result = "") :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dragon_curve_float_to_empty :
  ∀ (n : Float), dragon_curve n = "" :=
sorry

theorem dragon_curve_string_to_empty :
  ∀ (s : String), dragon_curve s = "" :=
sorry

theorem dragon_curve_base_case :
  dragon_curve 0 = "F" :=
sorry

theorem dragon_curve_length_increases :
  ∀ (n : Nat), n > 0 → String.length (dragon_curve n) > String.length (dragon_curve (n-1)) :=
sorry

theorem dragon_curve_chars_valid :
  ∀ (n : Nat), (dragon_curve n).all (fun c => c = 'F' ∨ c = 'R' ∨ c = 'L') :=
sorry
-- </vc-theorems>