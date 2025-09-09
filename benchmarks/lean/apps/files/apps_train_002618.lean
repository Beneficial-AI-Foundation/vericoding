def String.containsString (s₁ s₂ : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def word_search (query : String) (seq : List String) : List String :=
  sorry

theorem word_search_returns_nonempty (query : String) (seq : List String) : 
  word_search query seq ≠ [] := sorry

theorem word_search_none_means_no_matches (query : String) (seq : List String) :
  word_search query seq = ["None"] →
  ∀ x ∈ seq, ¬(String.containsString (String.toLower x) (String.toLower query)) := sorry

theorem word_search_results_contain_query (query : String) (seq : List String) :
  ∀ x ∈ word_search query seq, 
  word_search query seq ≠ ["None"] →
  String.containsString (String.toLower x) (String.toLower query) := sorry

theorem word_search_results_subset (query : String) (seq : List String) :
  ∀ x ∈ word_search query seq,
  word_search query seq ≠ ["None"] →
  x ∈ seq := sorry

theorem word_search_finds_all_matches (query : String) (seq : List String) :
  word_search query seq ≠ ["None"] →
  List.length (word_search query seq) = 
  List.length (List.filter (fun x => String.containsString (String.toLower x) (String.toLower query)) seq) := sorry

theorem word_search_empty_seq (query : String) :
  word_search query [] = ["None"] := sorry

/-
info: ['ab', 'abc', 'zab']
-/
-- #guard_msgs in
-- #eval word_search "ab" ["za", "ab", "abc", "zab", "zbc"]

/-
info: ['ab', 'abc', 'zab']
-/
-- #guard_msgs in
-- #eval word_search "aB" ["za", "ab", "abc", "zab", "zbc"]

/-
info: ['None']
-/
-- #guard_msgs in
-- #eval word_search "abcd" ["za", "aB", "Abc", "zAB", "zbc"]

-- Apps difficulty: introductory
-- Assurance level: unguarded