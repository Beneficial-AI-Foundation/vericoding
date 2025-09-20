-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_empty_for_nonpositive (n : Int) (h : n ≤ 0) :
  pattern n = "" :=
  sorry

theorem pattern_properties (n : Int) (h : n > 0) :
  let result := pattern n
  let lines := result.splitOn "\n"
  -- Number of lines matches input
  lines.length = n.toNat ∧
  -- Each line has correct total length
  (∀ line ∈ lines, line.length = (2*n - 1).toNat) ∧
  -- Each line has correct number of digits when stripped
  (∀ line ∈ lines, (line.trim).length = n.toNat) ∧
  -- All characters are valid digits when stripped
  (∀ line ∈ lines, ∀ c ∈ (line.trim).data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) ∧
  -- Correct spacing pattern
  (∀ (i : Fin lines.length), (lines[i]).startsWith (String.mk (List.replicate (n.toNat - i - 1) ' '))) ∧
  (∀ (i : Fin lines.length), (lines[i]).endsWith (String.mk (List.replicate i.val ' '))) ∧
  -- Same digit pattern on each line when stripped
  (∀ line ∈ lines, ∀ (i : Fin lines.length), line.trim = lines[i].trim) :=
  sorry
-- </vc-theorems>