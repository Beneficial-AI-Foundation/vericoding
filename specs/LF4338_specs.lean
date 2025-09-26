-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String := sorry

theorem nonpositive_returns_empty {n : Int} (h : n ≤ 0) :
  pattern n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_line_count {n : Int} (h : n > 0) : 
  ((pattern n).split fun c ↦ c = '\n').length = n := sorry

theorem pattern_line_width {n : Int} (h : n > 0) :
  ∀ line ∈ (pattern n).split fun c ↦ c = '\n', line.length = n := sorry

theorem pattern_first_line {n : Int} (h : n > 0) :
  let first := ((pattern n).split fun c ↦ c = '\n').get! 0
  ∀ c ∈ first.data, c = first.data[0]! := sorry

theorem pattern_diagonal_decrease {n : Int} (h : n > 0) :
  let lines := (pattern n).split fun c ↦ c = '\n'
  ∀ i ∈ List.range (min n.toNat 9),
    let curr := (lines.get! (i+1)).data[i+1]!.toString.toNat!
    let prev := (lines.get! i).data[i]!.toString.toNat!
    curr = prev - 1 ∨ (prev = 0 ∧ curr = 9) := sorry

theorem pattern_all_digits {n : Int} (h : n > 0) :
  let lines := (pattern n).split fun c ↦ c = '\n'
  ∀ line ∈ lines, ∀ c ∈ line.data, c.isDigit := sorry

theorem first_row_matches_input {n : Int} (h1 : n > 0) (h2 : n ≤ 9) :
  let first := ((pattern n).split fun c ↦ c = '\n').get! 0
  ∀ c ∈ first.data, c.toString.toNat! = n := sorry
-- </vc-theorems>