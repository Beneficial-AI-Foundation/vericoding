-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.lines (s : String) : List String := sorry
def pattern (n : Int) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>