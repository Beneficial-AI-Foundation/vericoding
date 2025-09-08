/-
Given a non-empty list of words, return the k most frequent elements.
Your answer should be sorted by frequency from highest to lowest. If two words have the same frequency, then the word with the lower alphabetical order comes first.

Example 1:

Input: ["i", "love", "leetcode", "i", "love", "coding"], k = 2
Output: ["i", "love"]
Explanation: "i" and "love" are the two most frequent words.
    Note that "i" comes before "love" due to a lower alphabetical order.

Example 2:

Input: ["the", "day", "is", "sunny", "the", "the", "the", "sunny", "is", "is"], k = 4
Output: ["the", "is", "sunny", "day"]
Explanation: "the", "is", "sunny" and "day" are the four most frequent words,
    with the number of occurrence being 4, 3, 2 and 1 respectively.

Note:

You may assume k is always valid, 1 ≤ k ≤ number of unique elements.
Input words contain only lowercase letters.

Follow up:

Try to solve it in O(n log k) time and O(n) extra space.
-/

-- <vc-helpers>
-- </vc-helpers>

def top_k_frequent (words : List String) (k : Nat) : List String :=
  sorry

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

-- Apps difficulty: interview
-- Assurance level: unguarded