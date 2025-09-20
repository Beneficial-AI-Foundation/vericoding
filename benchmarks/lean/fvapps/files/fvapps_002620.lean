-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_kiss (text : String) : String := sorry

theorem is_kiss_short_words (text : String) 
  (h₁ : text.split (· = ' ') |>.all (fun word => word.length ≤ 3)) 
  (h₂ : (text.split (· = ' ') |>.length) > 3)
  (h₃ : (text.split (· = ' ') |>.length) ≤ 10) :
  is_kiss text = "Good work Joe!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_kiss_long_words (text : String)
  (h₁ : text.split (· = ' ') |>.any (fun word => word.length ≥ 10))
  (h₂ : (text.split (· = ' ') |>.length) > 0)
  (h₃ : (text.split (· = ' ') |>.length) ≤ 5) :
  is_kiss text = "Keep It Simple Stupid" := sorry

theorem is_kiss_valid_output (text : String)
  (h : text.length > 0) :
  is_kiss text = "Keep It Simple Stupid" ∨ 
  is_kiss text = "Good work Joe!" := sorry
-- </vc-theorems>