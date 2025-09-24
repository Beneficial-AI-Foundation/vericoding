-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def top_k_frequent (words : List String) (k : Nat) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem top_k_frequent_properties_length 
  (words : List String) (k : Nat) (h : words ≠ []) :
  let result := top_k_frequent words k
  List.length result = k := sorry

theorem top_k_frequent_properties_subset
  (words : List String) (k : Nat) (h : words ≠ []) :
  let result := top_k_frequent words k
  ∀ x, x ∈ result → x ∈ words := sorry

theorem top_k_frequent_properties_unique
  (words : List String) (k : Nat) (h : words ≠ []) :
  let result := top_k_frequent words k
  ∀ x y, x ∈ result → y ∈ result → x = y → result.indexOf x = result.indexOf y := sorry

theorem top_k_frequent_properties_order
  (words : List String) (k : Nat) (h : words ≠ []) :
  let result := top_k_frequent words k
  let counts := (λ w => (words.filter (· = w)).length)
  ∀ i < result.length - 1,
    let curr := counts (result.get ⟨i, sorry⟩)
    let next := counts (result.get ⟨i+1, sorry⟩)
    curr > next ∨ (curr = next ∧ result.get ⟨i, sorry⟩ ≤ result.get ⟨i+1, sorry⟩) := sorry

theorem equal_frequencies_lexicographic_order
  (words : List String) (k : Nat) :
  let result := top_k_frequent words k
  let counts := (λ w => (words.filter (· = w)).length)
  ∀ i < result.length - 1,
    counts (result.get ⟨i, sorry⟩) = counts (result.get ⟨i+1, sorry⟩) →
    result.get ⟨i, sorry⟩ ≤ result.get ⟨i+1, sorry⟩ := sorry

/-
info: ['i', 'love']
-/
-- #guard_msgs in
-- #eval top_k_frequent ["i", "love", "leetcode", "i", "love", "coding"] 2

/-
info: ['the', 'is', 'sunny', 'day']
-/
-- #guard_msgs in
-- #eval top_k_frequent ["the", "day", "is", "sunny", "the", "the", "the", "sunny", "is", "is"] 4

/-
info: ['a']
-/
-- #guard_msgs in
-- #eval top_k_frequent ["a", "a", "b"] 1
-- </vc-theorems>