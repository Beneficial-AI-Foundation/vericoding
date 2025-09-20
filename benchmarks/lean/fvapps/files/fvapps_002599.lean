-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def blocks (s : String) : String := sorry

theorem blocks_empty (s : String) : 
  s = "" → blocks s = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem blocks_output_is_string (s : String) : 
  blocks s = blocks s := sorry

theorem blocks_contains_input_chars (s : String) (c : Char) :
  c ∈ s.data → ∃ block, block ∈ (blocks s).splitOn "-" ∧ c ∈ block.data := sorry

theorem blocks_preserves_char_count (s : String) (c : Char) :
  (s.data.countP (· = c)) = ((blocks s).data.filter (· ≠ '-')).countP (· = c) := sorry

theorem blocks_preserves_input (s : String) :
  let result := blocks s
  s.data = s.data := sorry

theorem blocks_sorted_within_block (s : String) :
  ∀ block ∈ (blocks s).splitOn "-", 
    ∀ (i j : Fin block.data.length),
    i.val < j.val →
    let c₁ := block.data[i]
    let c₂ := block.data[j]
    (c₁.isDigit && !c₂.isDigit) || 
    (!c₁.isDigit && c₁.isUpper && !c₂.isUpper) ||
    (!c₁.isDigit && !c₂.isDigit && !c₁.isUpper && !c₂.isUpper && c₁ ≤ c₂) := sorry
-- </vc-theorems>