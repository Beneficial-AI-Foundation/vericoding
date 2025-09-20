-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def super_pad (s : String) (w : Nat) (f : String := " ") : String := sorry

theorem default_padding_length 
  (s : String) (w : Nat) (f : String) 
  (h : ∀ c ∈ f.data, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '^') :
  let result := super_pad s w f
  (result.length = w) ∨ 
  (s.length > w ∧ result.length = w) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem right_padding
  (s : String) (w : Nat) (f : String)
  (h : ∀ c ∈ f.data, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '^') :
  let result := super_pad s w (">" ++ f)
  result.length = w ∧
  (s.length ≤ w → result.startsWith s) := sorry 

theorem center_padding
  (s : String) (w : Nat) (f : String)
  (h : ∀ c ∈ f.data, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '^') :
  let result := super_pad s w ("^" ++ f)
  result.length = w ∧ 
  (s.length ≤ w → ∃ l r : String, result = l ++ s ++ r) := sorry

theorem left_padding
  (s : String) (w : Nat) (f : String)
  (h : ∀ c ∈ f.data, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '^') :
  let result := super_pad s w ("<" ++ f)
  result.length = w ∧
  (s.length ≤ w → result.endsWith s) := sorry

theorem default_space_padding
  (s : String) (w : Nat) :
  super_pad s w = super_pad s w " " := sorry
-- </vc-theorems>