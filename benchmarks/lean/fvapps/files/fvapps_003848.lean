-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String := sorry

theorem pattern_non_positive_returns_empty (n : Int) (h : n ≤ 0) :
  pattern n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_returns_string (n : Int) :
  ∃ s : String, pattern n = s := sorry

theorem pattern_valid_properties {n : Int} (h : n > 0) :
  let result := pattern n
  let lines := String.splitOn result "\n"
  -- Number of lines is 2n - 1
  lines.length = (2 * n - 1).toNat ∧
  -- Each line is palindrome
  (∀ line ∈ lines, line.data = line.data.reverse) ∧ 
  -- All lines have same length
  (∀ line ∈ lines, line.length = lines[0]!.length) ∧
  -- All digits are 0-9
  (∀ c ∈ result.data, c.isDigit → (c.toNat - '0'.toNat) ≤ 9) ∧
  -- Top half equals reversed bottom half
  (lines.take n.toNat = (lines.drop (n-1).toNat).reverse)
  := sorry
-- </vc-theorems>