-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def capitals_first (s : String) : String := sorry

theorem capitals_first_output_format (s : String) 
  (h : s.length > 0) :
  let words := (capitals_first s).split (· = ' ')
  ∀ i < words.length - 1,
    ∀ w ∈ words[i]?,
      ∀ c ∈ w.get? 0,
        c.isLower →
        ∀ j, i < j → j < words.length →
          ∀ w' ∈ words[j]?,
            ∀ c' ∈ w'.get? 0,
              c'.isLower := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem capitals_first_basic_patterns {s : String}
  (h₁ : ∃ w ∈ (capitals_first s).split (· = ' '), ∃ c ∈ w.get? 0, c.isUpper) 
  (h₂ : ∃ w ∈ (capitals_first s).split (· = ' '), ∃ c ∈ w.get? 0, c.isLower) :
  ∃ i j,
    i < j ∧ 
    j < ((capitals_first s).split (· = ' ')).length ∧
    (∀ w ∈ ((capitals_first s).split (· = ' '))[i]?, ∀ c ∈ w.get? 0, c.isUpper) ∧
    (∀ w ∈ ((capitals_first s).split (· = ' '))[j]?, ∀ c ∈ w.get? 0, c.isLower) := sorry
-- </vc-theorems>