-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bucket_of (s : String) : String := sorry

theorem bucket_always_returns_valid_value (s : String) :
  bucket_of s = "water" ∨ bucket_of s = "slime" ∨ bucket_of s = "sludge" ∨ bucket_of s = "air" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem water_patterns_are_water (water_word : String) : 
  (water_word = "water" ∨ water_word = "wet" ∨ water_word = "wash") →
  bucket_of water_word = "water" ∧ bucket_of water_word.toUpper = "water" := sorry

theorem slime_patterns_are_slime :
  bucket_of "I don't know" = "slime" ∧ bucket_of "slime" = "slime" := sorry

theorem water_and_slime_make_sludge (water_word slime_word : String) :
  (water_word = "water" ∨ water_word = "wet" ∨ water_word = "wash") →
  (slime_word = "slime" ∨ slime_word = "I don't know") →
  bucket_of (water_word ++ " " ++ slime_word) = "sludge" ∧ 
  bucket_of (slime_word ++ " " ++ water_word) = "sludge" := sorry

theorem default_is_air (s : String) :
  s ≠ "water" →
  s ≠ "wet" →
  s ≠ "wash" →
  s ≠ "slime" →
  s ≠ "I don't know" →
  bucket_of s = "air" := sorry
-- </vc-theorems>