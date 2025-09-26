-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encrypt_message (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encrypt_message_alternating_pattern (s : String) (h : ∀ c ∈ s.data, 97 ≤ c.val ∧ c.val ≤ 122) :
  let result := encrypt_message s
  ∀ i < result.length - 1, i % 2 = 0 →
    Option.isSome (result.data[i]?) ∧ 
    (result.data[i]?.get!).isAlpha = true ∧
    Option.isSome (result.data[i+1]?) ∧
    (result.data[i+1]?.get!).isDigit = true
  := sorry

theorem encrypt_message_accurate_counts (s : String) (h : ∀ c ∈ s.data, 97 ≤ c.val ∧ c.val ≤ 122) :
  let result := encrypt_message s
  ∀ c ∈ s.data,
    let count := (s.data.filter (· = c)).length
    ∃ i < result.length,
      Option.isSome (result.data[i]?) ∧
      result.data[i]?.get! = c ∧
      Option.isSome (result.data[i+1]?) ∧
      String.toNat? (toString (result.data[i+1]?.get!)) = some count
  := sorry

theorem encrypt_message_preserves_order (s : String) (h : ∀ c ∈ s.data, 97 ≤ c.val ∧ c.val ≤ 122) :
  let result := encrypt_message s
  let input_first_occurrences := s.data.foldl (λ acc c => if c ∈ acc then acc else acc ++ [c]) []
  let result_chars := List.filter (λ c => c.isAlpha) result.data
  input_first_occurrences = result_chars
  := sorry

theorem encrypt_message_length (s : String) (h : s.length > 0) (h₂ : ∀ c ∈ s.data, 97 ≤ c.val ∧ c.val ≤ 122) :
  (encrypt_message s).length = 2 * (s.data.eraseDups).length
  := sorry

theorem encrypt_message_empty :
  encrypt_message "" = ""
  := sorry
-- </vc-theorems>