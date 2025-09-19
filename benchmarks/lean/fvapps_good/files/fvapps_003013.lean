-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longer (s : String) : String := sorry

instance : LE (Nat × String) where
  le := fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
-- </vc-definitions>

-- <vc-theorems>
theorem longer_sorted_property {s : String} {result : String} (h : result = longer s) 
  (h_nonempty : s ≠ "") :
  let words := result.split (· = ' ')
  ∀ i, i + 1 < words.length → 
    (words[i]!.length, words[i]!) ≤ (words[i+1]!.length, words[i+1]!)
  := sorry

theorem longer_preserves_unique_words {s : String} {result : String} 
  (h : result = longer s) :
  let input_words := s.split (· = ' ')
  let output_words := result.split (· = ' ')
  ∀ w, w ∈ input_words ↔ w ∈ output_words
  := sorry
-- </vc-theorems>