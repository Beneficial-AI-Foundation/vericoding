-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_company_name (oleg igor : String) : String := sorry

theorem output_length_matches_input
  (oleg igor : String)
  (h : oleg.length = igor.length) :
  (find_company_name oleg igor).length = oleg.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_uses_input_characters
  (oleg igor : String)
  (h : oleg.length = igor.length)
  (c : Char)
  (h2 : c ∈ (find_company_name oleg igor).data) :
  c ∈ oleg.data ∨ c ∈ igor.data := sorry

theorem identical_inputs_have_same_chars
  (s : String) :
  ∀ c, (c ∈ (find_company_name s s).data ↔ c ∈ s.data) := sorry

theorem output_preserves_min_char_counts
  (oleg igor : String)
  (h : oleg.length = igor.length) :
  let result := find_company_name oleg igor
  let oleg_turns := (oleg.length + 1) / 2
  let igor_turns := oleg.length / 2
  let oleg_result := (result.data.filter (· ∈ oleg.data)).length
  let igor_result := (result.data.filter (· ∈ igor.data)).length
  oleg_result ≥ oleg_turns ∧ igor_result ≥ igor_turns := sorry
-- </vc-theorems>