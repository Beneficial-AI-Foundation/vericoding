-- <vc-preamble>
def satisfies_triangle_inequality (n : Nat) (even_side : Nat) : Bool :=
  even_side < 2*n ∧ n + n > even_side
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_transform_triangle (n : Nat) : String := sorry

def has_integer_height (n : Nat) (even_side : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_format (n : Nat) (h : n > 0) :
  can_transform_triangle n = "YES" ∨ can_transform_triangle n = "NO" :=
sorry

theorem yes_case_valid (n : Nat) (h : n > 0) (h2 : can_transform_triangle n = "YES") :
  ∃ even_side : Nat,
    even_side % 2 = 0 ∧
    even_side ≥ 2 ∧
    even_side ≤ 2*n ∧
    satisfies_triangle_inequality n even_side ∧
    has_integer_height n even_side :=
sorry

theorem no_case_invalid (n : Nat) (h : n > 0) (h2 : can_transform_triangle n = "NO") :
  ∀ even_side : Nat,
    even_side % 2 = 0 →
    even_side ≥ 2 →
    even_side ≤ 2*n →
    ¬(satisfies_triangle_inequality n even_side ∧ has_integer_height n even_side) :=
sorry
-- </vc-theorems>