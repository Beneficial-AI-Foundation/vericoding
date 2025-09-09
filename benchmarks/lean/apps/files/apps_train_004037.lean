def pattern (n : Int) : String := sorry

def String.reverse (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def Nat.toString (n : Nat) : String := sorry

theorem pattern_invalid_n (n : Int) (h : n ≤ 0) :
  pattern n = "" := sorry

theorem pattern_valid_num_lines {n : Int} (h : n > 0) :
  let lines := String.splitOn (pattern n) "\n"
  lines.length = 2 * n - 1 := sorry

theorem pattern_valid_sequence {n : Int} (h : n > 0) :
  let lines := String.splitOn (pattern n) "\n"
  let mid := lines.length / 2
  ∀ i, i ≤ mid → 
    ∃ c, c ∈ String.toList (lines[i]!) ∧
    c = ((i + 1).toString.toList[0]!) := sorry

theorem pattern_reverse {n : Int} (h : n > 0) :
  let lines := String.splitOn (pattern n) "\n"
  let mid := lines.length / 2
  (lines.take mid).reverse = lines.drop (mid + 1) := sorry

theorem pattern_symmetric {n : Int} (h : n > 0) :
  let lines := String.splitOn (pattern n) "\n"
  ∀ line ∈ lines, line = line.reverse := sorry

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern 3

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern 4 2

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern -5 3

-- Apps difficulty: introductory
-- Assurance level: unguarded