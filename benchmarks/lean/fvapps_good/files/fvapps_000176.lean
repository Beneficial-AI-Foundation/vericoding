-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getLengthOfOptimalCompression (s : String) (k : Nat) : Nat := sorry

def naiveCompressionLength (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compressed_length_non_negative (s : String) (k : Nat) :
  getLengthOfOptimalCompression s k ≥ 0 := sorry

theorem compressed_length_not_longer_than_naive (s : String) (k : Nat) : 
  getLengthOfOptimalCompression s k ≤ naiveCompressionLength s := sorry

theorem compressed_length_not_longer_than_original (s : String) (k : Nat) :
  getLengthOfOptimalCompression s k ≤ s.length := sorry

theorem binary_string_min_length (s : String) (k : Nat) 
  (h1 : s.length > 0)
  (h2 : k < s.length)
  (h3 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b') :
  getLengthOfOptimalCompression s k ≥ 1 := sorry
-- </vc-theorems>