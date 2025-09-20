-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_format (n : Int) : String := sorry

theorem number_format_preserves_digits (n : Int) :
  let result := number_format n
  let digits := result.replace "," "" |>.replace "-" ""
  digits = toString n.natAbs := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem number_format_correct_sign (n : Int) :
  let result := number_format n
  (n < 0 → result.startsWith "-") ∧ 
  (n ≥ 0 → ¬result.startsWith "-") := sorry

theorem number_format_valid_commas (n : Int) :
  let result := number_format n
  let parts := (result.replace "-" "").splitOn ","
  (∀ p ∈ parts, p.length ≤ 3) ∧
  parts.head!.length ≤ 3 ∧
  (∀ p ∈ parts.tail, p.length = 3) := sorry

theorem number_format_roundtrip (n : Int) :
  let result := number_format n
  String.toInt! (result.replace "," "") = n := sorry
-- </vc-theorems>