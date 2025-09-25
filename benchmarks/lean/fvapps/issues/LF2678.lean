-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compress (s : String) : String := sorry

theorem compress_case_insensitive (s : String) : 
  compress s = compress s.toUpper ∧ compress s = compress s.toLower := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compress_only_digits (s : String) :
  s ≠ "" → compress s ≠ "" → 
  (∀ c : Char, c ∈ (compress s).data → c.isDigit) := by sorry

theorem compress_maps_repeat_words (s : String) (i : Nat) :
  s ≠ "" →
  let words := s.toLower.split (· = ' ')
  i < words.length →
  let result := compress s
  String.toNat! ((result.data.get! i).toString) = words.indexOf (words.get! i) := by sorry

/-
info: '012'
-/
-- #guard_msgs in
-- #eval compress "The bumble bee"

/-
info: '012012'
-/
-- #guard_msgs in
-- #eval compress "SILLY LITTLE BOYS silly little boys"

/-
info: '01234567802856734'
-/
-- #guard_msgs in
-- #eval compress "Ask not what your COUNTRY can do for you ASK WHAT YOU CAN DO FOR YOUR country"
-- </vc-theorems>