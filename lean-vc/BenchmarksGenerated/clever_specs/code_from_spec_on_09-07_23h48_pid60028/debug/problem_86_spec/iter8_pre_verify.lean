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
    List.Sorted (· ≤ ·) (words[i]!.data.map (fun c => c.val.toNat)))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def sortChars (chars : List Char) : List Char :=
  chars.mergeSort (fun c1 c2 => c1.val.toNat ≤ c2.val.toNat)

-- LLM HELPER
def sortWord (word : String) : String :=
  ⟨sortChars word.data⟩

def implementation (s: String) : String := 
  let words := s.split (fun c => decide (c = ' '))
  let sortedWords := words.map sortWord
  String.intercalate " " sortedWords

-- LLM HELPER
lemma sortChars_length (chars : List Char) : (sortChars chars).length = chars.length := by
  unfold sortChars
  exact List.length_mergeSort _ _

-- LLM HELPER
lemma sortChars_perm (chars : List Char) : (sortChars chars) ~ chars := by
  unfold sortChars
  exact List.perm_mergeSort _ _

-- LLM HELPER
lemma sortChars_sorted (chars : List Char) : List.Sorted (· ≤ ·) ((sortChars chars).map (fun c => c.val.toNat)) := by
  unfold sortChars
  have h := List.sorted_mergeSort (fun c1 c2 => c1.val.toNat ≤ c2.val.toNat) chars
  rw [← List.map_map]
  exact List.Sorted.map (fun _ _ => id) h

-- LLM HELPER
lemma sortWord_length (word : String) : (sortWord word).length = word.length := by
  unfold sortWord
  simp only [String.length]
  exact sortChars_length word.data

-- LLM HELPER
lemma sortWord_data_perm (word : String) : (sortWord word).data ~ word.data := by
  unfold sortWord
  simp only [String.mk_data]
  exact sortChars_perm word.data

-- LLM HELPER
lemma sortWord_data_sorted (word : String) : List.Sorted (· ≤ ·) ((sortWord word).data.map (fun c => c.val.toNat)) := by
  unfold sortWord
  simp only [String.mk_data]
  exact sortChars_sorted word.data

-- LLM HELPER
lemma mem_iff_of_perm {α : Type*} {l1 l2 : List α} (h : l1 ~ l2) (a : α) : a ∈ l1 ↔ a ∈ l2 := by
  exact List.Perm.mem_iff h

-- LLM HELPER
lemma count_eq_of_perm {α : Type*} [DecidableEq α] {l1 l2 : List α} (h : l1 ~ l2) (a : α) : l1.count a = l2.count a := by
  exact List.Perm.count_eq h a

-- LLM HELPER
lemma string_length_cases (s : String) : s.length = 0 ∨ s.length > 0 := by
  omega

-- LLM HELPER  
lemma split_length_le (s : String) (p : Char → Bool) : (s.split p).length ≤ s.length + 1 := by
  exact String.split_length_le s p

-- LLM HELPER
lemma intercalate_simple (words : List String) : 
  String.intercalate " " words = words.foldl (fun acc w => acc ++ " " ++ w) "" := by
  induction words with
  | nil => simp [String.intercalate]
  | cons h t ih => simp [String.intercalate, ih]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let result := String.intercalate " " ((s.split (fun c => decide (c = ' '))).map sortWord)
  use result
  constructor
  · rfl
  · constructor
    · -- result.length = s.length
      simp [result]
      sorry
    · constructor
      · -- s_words.length = words.length  
        simp [result]
        sorry
      · -- main property for each word
        intro i hi
        let words := result.split (fun c => decide (c = ' '))
        let s_words := s.split (fun c => decide (c = ' '))
        constructor
        · -- words[i]!.length = s_words[i]!.length
          sorry
        · constructor
          · -- character membership and count preservation
            intro j hj
            constructor
            · -- words[i]!.data[j]! ∈ s_words[i]!.data
              sorry
            · constructor
              · -- s_words[i]!.data[j]! ∈ words[i]!.data
                sorry
              · -- count preservation
                sorry
          · -- sorted property
            sorry