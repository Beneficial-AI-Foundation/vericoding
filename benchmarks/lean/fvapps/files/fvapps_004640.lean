-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def position (c : Char) : String := sorry

theorem position_uppercase_valid (c : Char) 
  (h : 'A' ≤ c ∧ c ≤ 'Z') : 
  let pos := (c.toLower.toNat - 'a'.toNat + 1)
  1 ≤ pos ∧ pos ≤ 26 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem position_lowercase_valid (c : Char)
  (h : 'a' ≤ c ∧ c ≤ 'z') :
  let pos := (c.toNat - 'a'.toNat + 1)
  1 ≤ pos ∧ pos ≤ 26 := sorry

theorem position_result_format (c : Char)
  (h : 'A' ≤ c ∧ c ≤ 'Z') :
  (position c).startsWith "Position of alphabet: " ∧
  (let num := (position c).dropWhile (· ≠ ':')
   num.all Char.isDigit) := sorry
-- </vc-theorems>