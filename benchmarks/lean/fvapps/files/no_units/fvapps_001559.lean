-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def converter (n : Float) (decimals : Nat := 0) (base : Float := 3.14159265359) : String := sorry

def intToFloat (n : Int) : Float := Float.ofInt n
-- </vc-definitions>

-- <vc-theorems>
theorem converter_sign_property {n : Float} {decimals : Nat} {base : Float}
  (h1 : -1000 ≤ n) (h2 : n ≤ 1000)
  (h3 : 1.1 ≤ base) (h4 : base ≤ 36) :
  (converter n decimals base).startsWith "-" = (n < 0) := sorry

theorem converter_decimal_property {n : Float} {decimals : Nat} {base : Float}
  (h1 : -1000 ≤ n) (h2 : n ≤ 1000)
  (h3 : 1.1 ≤ base) (h4 : base ≤ 36) :
  (converter n decimals base).contains '.' = (decimals > 0) := sorry

theorem converter_decimal_length {n : Float} {decimals : Nat} {base : Float}
  (h1 : -1000 ≤ n) (h2 : n ≤ 1000)
  (h3 : decimals > 0)
  (h4 : 1.1 ≤ base) (h5 : base ≤ 36) :
  ((converter n decimals base).split (· = '.')).getLast!.length = decimals := sorry

theorem converter_integer_no_decimal {n : Int}
  (h1 : -1000 ≤ n) (h2 : n ≤ 1000) :
  ¬(converter (intToFloat n) 0).contains '.' := sorry

theorem converter_default_base_is_pi {n : Float} {decimals : Nat}
  (h1 : -1000 ≤ n) (h2 : n ≤ 1000) :
  converter n decimals = converter n decimals 3.14159265359 := sorry

theorem converter_base_2_is_binary {n : Nat}
  (h : n ≤ 1000) :
  ∀ c ∈ (converter (intToFloat n) 0 2).data, c = '0' ∨ c = '1' := sorry
-- </vc-theorems>