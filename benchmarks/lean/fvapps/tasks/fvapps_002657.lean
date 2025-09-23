-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unusual_lex_order (words: List String) : List String :=
  sorry

def reverse (s: String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input (words: List String) (h: words.length > 0) :
  (unusual_lex_order words).length = words.length :=
sorry

theorem output_contains_same_elements (words: List String) (h: words.length > 0) :
  ∀ x, (x ∈ unusual_lex_order words ↔ x ∈ words) :=
sorry

theorem reverse_sorted_by_reversed_strings (words: List String) (h: words.length > 0) :
  ∀ (i: Nat) (h': i + 1 < (unusual_lex_order words).length),
    let result := unusual_lex_order words
    Option.isSome (result[i]?) ∧ Option.isSome (result[i+1]?) →
    reverse (Option.get! result[i]?) ≤ reverse (Option.get! result[i+1]?) :=
sorry

theorem idempotent (words: List String) (h: words.length > 0) :
  unusual_lex_order (unusual_lex_order words) = unusual_lex_order words :=
sorry
-- </vc-theorems>