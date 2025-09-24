-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def increment_string (s : String) : String := sorry

theorem increment_string_length (text : String) (num : Nat) (leading_zeros : Nat)
  (h : num ≤ 999999) (h2 : leading_zeros ≤ 5) :
  String.length (increment_string (text ++ 
    (if num > 0 then String.mk (List.replicate leading_zeros '0') ++ toString num else ""))) ≥ 
  String.length (text ++ 
    (if num > 0 then String.mk (List.replicate leading_zeros '0') ++ toString num else "")) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem increment_string_preserves_prefix (text : String) (num : Nat) (leading_zeros : Nat)
  (h : num ≤ 999999) (h2 : leading_zeros ≤ 5) :
  (increment_string (text ++ 
    (if num > 0 then String.mk (List.replicate leading_zeros '0') ++ toString num else ""))).startsWith text := sorry

theorem increment_string_increments_number (text : String) (num : Nat) (leading_zeros : Nat)
  (h : num ≤ 999999) (h2 : leading_zeros ≤ 5) :
  ∀ suffix : String,
  suffix.all Char.isDigit →
  String.toNat! (String.drop (increment_string (text ++ suffix)) text.length) = 
  String.toNat! suffix + 1 := sorry

theorem increment_string_no_numbers (s : String)
  (h : ∀ c ∈ s.data, !c.isDigit) :
  increment_string s = s ++ "1" := sorry

theorem increment_string_just_digits (digits : List Nat)
  (h : ∀ d ∈ digits, d ≤ 9) 
  (h2 : digits ≠ []) :
  let num := String.mk (digits.map Char.ofNat)
  String.length (increment_string num) ≥ String.length num ∧
  String.toNat! (increment_string num) = String.toNat! num + 1 := sorry
-- </vc-theorems>