-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def b (n : Int) : String :=
sorry

def d (s : String) : Int :=
sorry

def skrzat (mode : String) (input : Int ⊕ String) : String :=
sorry

def is_valid_binary (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bidirectional_conversion : ∀ (n : Int),
  let bin := b n; d bin = n :=
sorry

theorem binary_valid : ∀ (n : Int),
  is_valid_binary (b n) = true :=
sorry

theorem skrzat_binary_format : ∀ (binary : String),
  is_valid_binary binary = true →
  ∃ n : Int, skrzat "b" (Sum.inr binary) = s!"From binary: {binary} is {n}" :=
sorry

theorem skrzat_decimal_format : ∀ (decimal : Int),
  ∃ binary : String,
    skrzat "d" (Sum.inl decimal) = s!"From decimal: {decimal} is {binary}" ∧
    is_valid_binary binary = true :=
sorry

theorem skrzat_invalid_base : ∀ (input : Int ⊕ String),
  skrzat "x" input ≠ skrzat "d" input ∧ skrzat "x" input ≠ skrzat "b" input :=
sorry

theorem positive_conversion : ∀ (n : Int),
  n ≥ 0 →
  let bin := b n
  ¬bin.startsWith "-" ∧ d bin = n :=
sorry

theorem zero_negative_conversion : ∀ (n : Int),
  n ≤ 0 →
  let bin := b n
  d bin = n :=
sorry
-- </vc-theorems>