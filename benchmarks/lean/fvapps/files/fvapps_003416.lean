-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def join (chars : List (Nat × String)) : String := sorry

def run_length_encoding (s : String) : List (Nat × String) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rle_valid_pairs (s : String) :
  ∀ pair ∈ run_length_encoding s,
  ∃ (n : Nat) (c : String), pair = (n, c) := sorry

theorem rle_positive_counts (s : String) :
  ∀ (n : Nat) (c : String), (n, c) ∈ run_length_encoding s → n > 0 := sorry 

theorem rle_adjacent_chars_differ (s : String) :
  ∀ (n₁ n₂ : Nat) (c₁ c₂ : String),
  let encoded := run_length_encoding s
  let pairs := List.zip encoded (encoded.tail)
  ((n₁, c₁), (n₂, c₂)) ∈ pairs → c₁ ≠ c₂ := sorry

theorem rle_decode_matches_input (s : String) :
  join (run_length_encoding s) = s := sorry

theorem rle_empty_string :
  run_length_encoding "" = [] := sorry
-- </vc-theorems>