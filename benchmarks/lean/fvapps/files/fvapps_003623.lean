-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_without_loss (text : String) (split_chars : String) : List String := sorry

theorem split_without_loss_returns_nonempty_segments 
  (text : String) (split_chars : String) 
  (h1 : text.length > 0) (h2 : split_chars.length > 0) : 
  let result := split_without_loss text split_chars 
  ∀ segment ∈ result, segment.length > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_with_pipe_returns_nonempty_segments
  (text : String)
  (h : text.length > 0) :
  let result := split_without_loss text "|"
  ∀ segment ∈ result, segment.length > 0 := sorry
-- </vc-theorems>