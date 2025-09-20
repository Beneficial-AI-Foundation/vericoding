-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_irreducible_anagram (s: String) (queries: List (Nat × Nat)) : List Bool := sorry

theorem output_length_correct (s: String) (queries: List (Nat × Nat)) :
  let result := has_irreducible_anagram s queries
  result.length = queries.length ∧ 
  result.all (fun x => x = true ∨ x = false) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_query_true (s: String) (queries: List (Nat × Nat)) :
  let result := has_irreducible_anagram s queries
  ∀ (i : Nat), i < queries.length →
    let (l,r) := queries.get! i
    l = r → result.get! i = true := sorry

theorem full_string_single_char_false (s: String) :
  s.length ≥ 2 →
  (∀ (i : Nat), i < s.length → s.get ⟨i⟩ = s.get ⟨0⟩) → 
  has_irreducible_anagram s [(1, s.length)] = [false] := sorry

theorem different_endpoints_true (s: String) (queries: List (Nat × Nat)) :
  let result := has_irreducible_anagram s queries
  ∀ (i : Nat), i < queries.length →
    let (l,r) := queries.get! i
    l ≤ s.length → r ≤ s.length →
    l > 0 → r > 0 →
    s.get ⟨l-1⟩ ≠ s.get ⟨r-1⟩ → result.get! i = true := sorry
-- </vc-theorems>