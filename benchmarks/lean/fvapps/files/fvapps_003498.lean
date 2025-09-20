-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def read_out (words : List String) : String := sorry

theorem read_out_length_matches_input (words : List String) 
  (h : List.length words > 0) (h2 : ∀ w ∈ words, String.length w > 0) : 
  String.length (read_out words) = List.length words := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem read_out_takes_first_chars (words : List String) 
  (h : List.length words > 0) (h2 : ∀ w ∈ words, String.length w > 0) :
  ∀ i < words.length, String.data (read_out words) = (String.get! (List.get! words i) 0) :: (String.data (read_out words)) := sorry

theorem read_out_preserves_uppercase (words : List String)
  (h : List.length words > 0)
  (h2 : ∀ w ∈ words, String.length w > 0)
  (h3 : ∀ w ∈ words, ∀ c ∈ w.data, 'A'.val ≤ c.val ∧ c.val ≤ 'Z'.val) :
  ∀ c ∈ (read_out words).data, 'A'.val ≤ c.val ∧ c.val ≤ 'Z'.val := sorry

theorem read_out_preserves_lowercase (words : List String)
  (h : List.length words > 0)
  (h2 : ∀ w ∈ words, String.length w > 0)
  (h3 : ∀ w ∈ words, ∀ c ∈ w.data, 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val) :
  ∀ c ∈ (read_out words).data, 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val := sorry

theorem read_out_empty_list :
  read_out [] = "" := sorry
-- </vc-theorems>