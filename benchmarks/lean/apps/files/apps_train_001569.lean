def CHARS := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F']

def int_to_base_n (num : Nat) (base : Nat) : String :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def is_polydivisible (s : String) (base : Nat) : Bool :=
sorry

theorem single_digit_polydivisible {base : Nat} (h1 : base ≥ 2) (h2 : base ≤ CHARS.length) :
  ∀ (digit : Char), digit ∈ CHARS.take base → is_polydivisible digit.toString base :=
sorry

theorem base_conversion_result_bool {base : Nat} (h1 : base ≥ 2) (h2 : base ≤ CHARS.length) 
  (decimal_num : Nat) :
  let base_n := int_to_base_n decimal_num base
  ∃ (b : Bool), is_polydivisible base_n base = b :=
sorry

theorem zero_polydivisible {base : Nat} (h1 : base ≥ 2) (h2 : base ≤ CHARS.length) :
  is_polydivisible "0" base = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_polydivisible "123" 10

/-
info: False
-/
-- #guard_msgs in
-- #eval is_polydivisible "1234" 10

/-
info: True
-/
-- #guard_msgs in
-- #eval is_polydivisible "123220" 6

-- Apps difficulty: interview
-- Assurance level: unguarded