import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
      s_words[i]!.data[j]! ∈ words[i]!.data ∧
      words[i]!.data.count (words[i]!.data[j]!) = s_words[i]!.data.count (s_words[i]!.data[j]!))) ∧
    List.Sorted Nat.le (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def sortStringChars (s: String) : String :=
  String.mk (s.data.mergeSort (fun c1 c2 => c1.val.toNat ≤ c2.val.toNat))

def implementation (s: String) : String := 
  let words := s.split (fun c => c = ' ')
  let sortedWords := words.map sortStringChars
  String.intercalate " " sortedWords

-- LLM HELPER
lemma sortStringChars_length (s: String) : (sortStringChars s).length = s.length := by
  simp [sortStringChars, String.length, List.length_mergeSort]

-- LLM HELPER
lemma sortStringChars_data_perm (s: String) : (sortStringChars s).data ~ s.data := by
  simp [sortStringChars]
  exact List.perm_mergeSort _ _

-- LLM HELPER
lemma sortStringChars_sorted (s: String) : List.Sorted Nat.le ((sortStringChars s).data.map (fun c => c.val.toNat)) := by
  simp [sortStringChars]
  have h := List.sorted_mergeSort s.data (fun c1 c2 => c1.val.toNat ≤ c2.val.toNat)
  rw [← List.map_map]
  apply List.Sorted.map
  · exact h
  · intros a b hab
    exact hab

-- LLM HELPER
lemma mem_of_perm {α : Type*} [DecidableEq α] {l1 l2 : List α} (h : l1 ~ l2) (x : α) : x ∈ l1 ↔ x ∈ l2 := by
  exact List.mem_of_perm h

-- LLM HELPER
lemma count_of_perm {α : Type*} [DecidableEq α] {l1 l2 : List α} (h : l1 ~ l2) (x : α) : l1.count x = l2.count x := by
  exact List.count_eq_of_perm h

-- LLM HELPER
lemma split_intercalate_space (words: List String) :
  (String.intercalate " " words).split (fun c => c = ' ') = words := by
  induction words with
  | nil => simp [String.intercalate, String.split]
  | cons h t ih => 
    cases t with
    | nil => simp [String.intercalate, String.split]
    | cons h' t' => 
      simp [String.intercalate, String.split]
      exact ih

-- LLM HELPER
lemma intercalate_length_basic (words: List String) :
  (String.intercalate " " words).length ≥ (words.map String.length).sum := by
  induction words with
  | nil => simp [String.intercalate]
  | cons h t ih =>
    cases t with
    | nil => simp [String.intercalate]
    | cons h' t' =>
      simp [String.intercalate]
      omega

-- LLM HELPER
lemma string_split_intercalate_length_helper (s: String) (words: List String) :
  s.split (fun c => c = ' ') = words →
  (String.intercalate " " (words.map sortStringChars)).length = s.length := by
  intro h
  have h1 : (words.map sortStringChars).map String.length = words.map String.length := by
    simp [List.map_map, sortStringChars_length]
  rw [← h]
  simp [String.length]
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
  let words := s.split (fun c => c = ' ')
  let sortedWords := words.map sortStringChars
  let result := String.intercalate " " sortedWords
  use result
  constructor
  · rfl
  · simp only [result]
    constructor
    · -- Length equality
      exact string_split_intercalate_length_helper s words rfl
    · constructor
      · -- Word count equality
        rw [split_intercalate_space]
        simp [List.length_map]
      · -- Properties of each word
        intro i hi
        rw [split_intercalate_space] at hi ⊢
        simp [List.getElem_map]
        constructor
        · -- Length equality for each word
          exact sortStringChars_length _
        · constructor
          · -- Character membership and count preservation
            intro j hj
            simp [sortStringChars_length] at hj
            constructor
            · -- Character from sorted word is in original word
              have h_perm := sortStringChars_data_perm (words[i]!)
              rw [← mem_of_perm h_perm]
              simp [List.getElem_mem]
            · constructor
              · -- Character from original word is in sorted word
                have h_perm := sortStringChars_data_perm (words[i]!)
                rw [mem_of_perm h_perm]
                simp [List.getElem_mem]
              · -- Count preservation
                have h_perm := sortStringChars_data_perm (words[i]!)
                exact count_of_perm h_perm _
          · -- Sorted property
            exact sortStringChars_sorted (words[i]!)