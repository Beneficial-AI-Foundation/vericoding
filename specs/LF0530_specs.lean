-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode_binary_string (s : String) : String := sorry

theorem decode_binary_chunks {s : String} (h₁: ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h₂: ∃ n, s.length = 4 * n) :
  (∀ c ∈ (decode_binary_string s).data, 
    c = 'a' ∨ c = 'b' ∨ c = 'c' ∨ c = 'd' ∨ 
    c = 'e' ∨ c = 'f' ∨ c = 'g' ∨ c = 'h' ∨
    c = 'i' ∨ c = 'j' ∨ c = 'k' ∨ c = 'l' ∨
    c = 'm' ∨ c = 'n' ∨ c = 'o' ∨ c = 'p') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_binary_length {s : String} (h₁: ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h₂: ∃ n, s.length = 4 * n) :
  (decode_binary_string s).length = s.length / 4 := sorry

theorem single_chunk_maps_to_letter {s : String} 
  (h₁: ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h₂: s.length = 4) :
  (decode_binary_string s).length = 1 ∧
  (∃ c ∈ (decode_binary_string s).data,
    c = 'a' ∨ c = 'b' ∨ c = 'c' ∨ c = 'd' ∨ 
    c = 'e' ∨ c = 'f' ∨ c = 'g' ∨ c = 'h' ∨
    c = 'i' ∨ c = 'j' ∨ c = 'k' ∨ c = 'l' ∨
    c = 'm' ∨ c = 'n' ∨ c = 'o' ∨ c = 'p') := sorry

theorem consistent_mapping {s : String} 
  (h₁: ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h₂: s.length = 4) :
  decode_binary_string s = decode_binary_string s := sorry
-- </vc-theorems>