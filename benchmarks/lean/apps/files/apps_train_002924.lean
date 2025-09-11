-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String := sorry

theorem pattern_non_positive (n : Int) (h : n ≤ 0) : pattern n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_lines_count (n : Int) (h : 1 ≤ n ∧ n ≤ 9) :
  let lines := (pattern n).splitOn "\n"
  lines.length = n.toNat := sorry

theorem pattern_line_content (n : Int) (i : Nat) (h1 : 1 ≤ n ∧ n ≤ 9) (h2 : 0 ≤ i ∧ i < n) :
  let lines := (pattern n).splitOn "\n"
  let line := lines[i]'(by sorry)
  let nums := line.data.map (λ c => c.toNat - '0'.toNat)
  nums = List.range' (i + 1) (n.toNat + 1) := sorry

theorem pattern_no_extra_whitespace (n : Int) (h : 1 ≤ n ∧ n ≤ 9) :
  let result := pattern n
  let lines := result.splitOn "\n"
  ¬result.startsWith "\n" ∧ 
  ¬result.endsWith "\n" ∧
  ∀ line ∈ lines, ¬(line.data.contains ' ' ∧ line.data.contains ' ') := sorry

/-
info: '12\n2'
-/
-- #guard_msgs in
-- #eval pattern 2

/-
info: '1234\n234\n34\n4'
-/
-- #guard_msgs in
-- #eval pattern 4

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded