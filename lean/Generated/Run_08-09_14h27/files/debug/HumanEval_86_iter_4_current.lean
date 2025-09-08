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

-- LLM HELPER
def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) : Prop :=
-- spec
let spec (result : String) :=
  result.length = s.length ∧
  let words := result.split (fun c => c = ' ')
  let s_words := s.split (fun c => c = ' ')
  s_words.length = words.length ∧
  ∀ i, i < words.length →
    words[i]!.length = s_words[i]!.length ∧
    ((∀ j, j < words[i]!.length →
      (words[i]!.data[j]! ∈ s_words[i]!.data ∧
      s_words[i]!.data[j]! ∈ words[i]!.data ∧
      words[i]!.data.count (words[i]!.data[j]!) = s_words[i]!.data.count (s_words[i]!.data[j]!))) ∧
    List.Sorted Nat.le (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma sortStringChars_same_length (s : String) : (sortStringChars s).length = s.length := by
  unfold sortStringChars String.length
  simp [List.length_mergeSort]

-- LLM HELPER
lemma sortStringChars_same_chars (s : String) : (sortStringChars s).data.toFinset = s.data.toFinset := by
  unfold sortStringChars
  simp [List.mergeSort_eq_toFinset]

-- LLM HELPER  
lemma sortStringChars_sorted (s : String) : List.Sorted Nat.le ((sortStringChars s).data.map (fun c => c.val.toNat)) := by
  unfold sortStringChars
  apply List.Sorted.map
  · apply List.sorted_mergeSort
  · intros a b h
    simp at h
    exact Nat.le_of_ble_eq_true h

-- LLM HELPER
lemma sortStringChars_count_eq (s : String) (c : Char) : 
  (sortStringChars s).data.count c = s.data.count c := by
  unfold sortStringChars
  exact List.count_mergeSort _ _

-- LLM HELPER
lemma split_intercalate_simple (words : List String) : 
  words ≠ [] → (String.intercalate " " words).split (fun c => c = ' ') = words := by
  intro h
  cases words with
  | nil => contradiction
  | cons head tail =>
    cases tail with
    | nil => 
      simp [String.intercalate, String.split]
      rfl
    | cons _ _ => 
      simp [String.intercalate, String.split]
      rfl

-- LLM HELPER
lemma implementation_preserves_structure (s : String) :
  let result := implementation s
  let words := result.split (fun c => c = ' ')
  let s_words := s.split (fun c => c = ' ')
  s_words.length = words.length := by
  unfold implementation
  simp
  by_cases h : s.split (fun c => c = ' ') = []
  · simp [h]
    rfl
  · have h_map_len : (List.map sortStringChars (s.split (fun c => c = ' '))).length = (s.split (fun c => c = ' ')).length := by simp
    have h_nonempty : List.map sortStringChars (s.split (fun c => c = ' ')) ≠ [] := by
      simp [List.map_eq_nil_iff]
      exact h
    have := split_intercalate_simple (List.map sortStringChars (s.split (fun c => c = ' '))) h_nonempty
    rw [this]
    simp

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    constructor
    · simp [String.length]
      have : ∀ w ∈ s.split (fun c => c = ' '), (sortStringChars w).length = w.length := by
        intros w _
        exact sortStringChars_same_length w
      simp [this]
      rfl
    · constructor
      · exact implementation_preserves_structure s
      · intro i hi
        constructor
        · simp
          have : ∀ w ∈ s.split (fun c => c = ' '), (sortStringChars w).length = w.length := by
            intros w _
            exact sortStringChars_same_length w
          simp [this]
          rfl
        · constructor
          · intro j hj
            constructor
            · simp
              have : ∀ w ∈ s.split (fun c => c = ' '), (sortStringChars w).data.toFinset = w.data.toFinset := by
                intros w _
                exact sortStringChars_same_chars w
              simp [this]
              rfl
            · constructor  
              · simp
                have : ∀ w ∈ s.split (fun c => c = ' '), (sortStringChars w).data.toFinset = w.data.toFinset := by
                  intros w _
                  exact sortStringChars_same_chars w
                simp [this]
                rfl
              · simp
                have : ∀ w ∈ s.split (fun c => c = ' '), ∀ c, (sortStringChars w).data.count c = w.data.count c := by
                  intros w _ c
                  exact sortStringChars_count_eq w c
                simp [this]
                rfl
          · simp
            have : ∀ w ∈ s.split (fun c => c = ' '), List.Sorted Nat.le ((sortStringChars w).data.map (fun c => c.val.toNat)) := by
              intros w _
              exact sortStringChars_sorted w
            simp [this]
            rfl