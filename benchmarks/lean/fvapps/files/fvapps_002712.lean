-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gordon (s : String) : String := sorry

-- Theorem for the ending
-- </vc-definitions>

-- <vc-theorems>
theorem gordon_ends_with_bangs {s : String} (h : s ≠ "") :
  (gordon s).endsWith "!!!!" := sorry

-- Theorem for no vowels

theorem gordon_no_vowels {s : String} (h : s ≠ "") :
  ∀ c ∈ (gordon s).data, c ≠ 'A' ∧ c ≠ 'E' ∧ c ≠ 'I' ∧ c ≠ 'O' ∧ c ≠ 'U' := sorry

-- Theorem for length

theorem gordon_length {s : String} (h : s ≠ "") :
  (gordon s).length ≥ s.length := sorry

-- Theorem for non-empty parts

theorem gordon_parts_nonempty {s : String} (h : s ≠ "") :
  let parts := (gordon s).dropRight 4
  ∀ p ∈ parts.split (· = '!'), p ≠ "" := sorry
-- </vc-theorems>