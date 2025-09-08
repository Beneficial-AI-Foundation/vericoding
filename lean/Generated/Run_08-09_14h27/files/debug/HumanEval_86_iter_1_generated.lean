/- 
function_signature: "def anti_shuffle(s : str) -> str"
docstring: |
    """
    Write a function that takes a string and returns an ordered version of it.
    Ordered version of string, is a string where all words (separated by space)
    are replaced by a new word where all the characters arranged in
    ascending order based on ascii value.
    Note: You should keep the order of words and blank spaces in the sentence.
test_cases:
  - input: "Hi"
    output: "Hi"
  - input: "hello"
    output: "ehllo"
  - input: "Hello World!!!"
    output: "Hello !!!Wdlor"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sortStringChars (s : String) : String := 
  String.mk (s.data.mergeSort (fun c1 c2 => c1.val ≤ c2.val))

def implementation (s: String) : String :=
  let words := s.split (fun c => c = ' ')
  let sortedWords := words.map sortStringChars
  String.intercalate " " sortedWords

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  result.length = s.length ∧
  let words := result.split (fun c => c = ' ');
  let s_words := s.split (fun c => c = ' ');
  s_words.length = words.length ∧
  ∀ i, i < words.length →
    words[i]!.length = s_words[i]!.length ∧
    ((∀ j, j < words[i]!.length →
      (words[i]!.data[j]! ∈ s_words[i]!.data ∧
      s_words[i]!data[j]! ∈ words[i]!.data ∧
      words[i]!.data.count (words[i]!.data[j]!) = s_words[i]!.data.count (s_words[i]!.data[j]!))) ∧
    List.Sorted Nat.le (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma sortStringChars_same_length (s : String) : (sortStringChars s).length = s.length := by
  simp [sortStringChars, String.length]
  rw [List.length_mergeSort]

-- LLM HELPER
lemma sortStringChars_same_chars (s : String) : (sortStringChars s).data.toFinset = s.data.toFinset := by
  simp [sortStringChars]
  rw [List.toFinset_mergeSort]

-- LLM HELPER  
lemma sortStringChars_sorted (s : String) : List.Sorted Nat.le ((sortStringChars s).data.map (fun c => c.val.toNat)) := by
  simp [sortStringChars]
  apply List.Sorted.map
  apply List.sorted_mergeSort
  intros a b h
  exact Nat.le_of_succ_le_succ h

-- LLM HELPER
lemma sortStringChars_count_eq (s : String) (c : Char) : 
  (sortStringChars s).data.count c = s.data.count c := by
  simp [sortStringChars]
  rw [List.count_mergeSort]

-- LLM HELPER
lemma split_intercalate_length (words : List String) : 
  (String.intercalate " " words).split (fun c => c = ' ') = words := by
  induction words with
  | nil => simp [String.intercalate]
  | cons head tail ih =>
    cases tail with
    | nil => simp [String.intercalate]
    | cons _ _ => 
      simp [String.intercalate]
      sorry -- This requires more detailed string manipulation lemmas

-- LLM HELPER
lemma implementation_preserves_structure (s : String) :
  let result := implementation s
  let words := result.split (fun c => c = ' ')
  let s_words := s.split (fun c => c = ' ')
  s_words.length = words.length := by
  simp [implementation]
  have h := split_intercalate_length (s.split (fun c => c = ' ')).map sortStringChars
  sorry -- Requires more work on string splitting/joining

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp only [implementation]
    constructor
    · -- Length preservation
      sorry -- This requires showing that sorting and rejoining preserves length
    · constructor
      · -- Number of words preservation  
        exact implementation_preserves_structure s
      · -- Properties of individual words
        intro i hi
        constructor
        · -- Length of each word preserved
          sorry
        · constructor
          · -- Character membership and counts preserved
            intro j hj
            constructor
            · -- Character in sorted word is in original word
              sorry
            · constructor  
              · -- Character in original word is in sorted word
                sorry
              · -- Character counts preserved
                sorry
          · -- Words are sorted
            sorry