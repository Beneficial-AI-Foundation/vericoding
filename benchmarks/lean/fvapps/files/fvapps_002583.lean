-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (s : String) : String := sorry 
def decode (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_length_preserving (s : String) : 
  (encode s).length = s.length := sorry

theorem decode_length_preserving (s : String) :
  (decode s).length = s.length := sorry

theorem encode_non_vowels_unchanged (s : String) :
  ∀ c, c ∈ s.data → c ∉ ['a', 'e', 'i', 'o', 'u'] → 
  c ∈ (encode s).data := sorry

theorem decode_non_numbers_unchanged (s : String) :
  ∀ c, c ∈ s.data → c ∉ ['1', '2', '3', '4', '5'] →
  c ∈ (decode s).data := sorry
-- </vc-theorems>