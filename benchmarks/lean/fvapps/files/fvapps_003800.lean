-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def basic_op (op : String) (x y : Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_property (x y : Float) : ¬ x.isNaN → ¬ y.isNaN → ¬ x.isInf → ¬ y.isInf →
  basic_op "+" x y = x + y :=
  sorry

theorem sub_property (x y : Float) : ¬ x.isNaN → ¬ y.isNaN → ¬ x.isInf → ¬ y.isInf →
  basic_op "-" x y = x - y :=
  sorry

theorem mult_property (x y : Float) : ¬ x.isNaN → ¬ y.isNaN → ¬ x.isInf → ¬ y.isInf →
  basic_op "*" x y = x * y :=
  sorry

theorem div_property (x y : Float) : ¬ x.isNaN → ¬ y.isNaN → ¬ x.isInf → ¬ y.isInf → y ≠ 0 →
  basic_op "/" x y = x / y :=
  sorry

theorem invalid_operator (op : String) (x y : Float) : 
  op ≠ "+" → op ≠ "-" → op ≠ "*" → op ≠ "/" →
  (basic_op op x y).isNaN :=
  sorry
-- </vc-theorems>