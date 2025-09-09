-- <vc-helpers>
-- </vc-helpers>

def String.lines (s : String) : List String := sorry
def pattern (n : Int) : String := sorry

theorem pattern_positive_input_line_count {n : Int} (h : n > 0) : 
  (pattern n).lines.length = n := sorry

theorem pattern_negative_input_empty {n : Int} (h : n ≤ 0) :
  pattern n = "" := sorry

theorem pattern_each_line_starts_with_n {n : Int} (h : n > 0) :
  let lines := (pattern n).lines
  ∀ line ∈ lines, line.get! 0 = (Char.ofNat (n.toNat + 48)) := sorry

theorem pattern_last_line_is_descending {n : Int} (h : n > 0) :
  let lines := (pattern n).lines
  let last := lines.getLast!
  last = String.mk (List.range n.toNat |>.map (fun i => Char.ofNat (i + 49))) := sorry

theorem pattern_lines_start_with_same_digit {n : Int} (h : n > 0) :
  let lines := (pattern n).lines
  ∀ i : Nat, i + 1 < lines.length → 
    lines[i]!.get! 0 = lines[i + 1]!.get! 0 := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval pattern 1

/-
info: '2\n21'
-/
-- #guard_msgs in
-- #eval pattern 2

/-
info: expected
-/
-- #guard_msgs in
-- #eval pattern 4

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern 0

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern -1

-- Apps difficulty: introductory
-- Assurance level: unguarded