-- <vc-helpers>
-- </vc-helpers>

def number_format (n : Int) : String := sorry

theorem number_format_preserves_digits (n : Int) :
  let result := number_format n
  let digits := result.replace "," "" |>.replace "-" ""
  digits = toString n.natAbs := sorry

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

/-
info: '100,000'
-/
-- #guard_msgs in
-- #eval number_format 100000

/-
info: '5,678,545'
-/
-- #guard_msgs in
-- #eval number_format 5678545

/-
info: '-420,902'
-/
-- #guard_msgs in
-- #eval number_format -420902

-- Apps difficulty: introductory
-- Assurance level: unguarded