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
lemma string_split_intercalate (words : List String) : 
  (String.intercalate " " words).split (fun c => decide (c = ' ')) = words := by
  simp [String.intercalate]
  induction words with
  | nil => simp
  | cons h t ih => 
    simp [String.intercalate]
    cases t with
    | nil => simp
    | cons _ _ => simp [ih]

-- LLM HELPER
lemma string_intercalate_length (words : List String) : 
  (String.intercalate " " words).length = words.foldl (fun acc w => acc + w.length) 0 + (if words.length > 0 then words.length - 1 else 0) := by
  simp [String.intercalate]
  induction words with
  | nil => simp
  | cons h t ih => 
    simp [String.intercalate]
    cases t with
    | nil => simp
    | cons _ _ => simp [ih]; omega

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
      have h1 : result.split (fun c => decide (c = ' ')) = (s.split (fun c => decide (c = ' '))).map sortWord := by
        simp [result]
        exact string_split_intercalate ((s.split (fun c => decide (c = ' '))).map sortWord)
      have h2 : ∀ i, i < (s.split (fun c => decide (c = ' '))).length → 
        ((s.split (fun c => decide (c = ' '))).map sortWord)[i]!.length = (s.split (fun c => decide (c = ' ')))[i]!.length := by
        intro i hi
        simp [List.getElem_map]
        exact sortWord_length _
      have h3 : (s.split (fun c => decide (c = ' '))).map sortWord = (s.split (fun c => decide (c = ' '))).map sortWord := rfl
      -- Use the fact that each word length is preserved
      omega
    · constructor
      · -- s_words.length = words.length  
        simp [result]
        have h : result.split (fun c => decide (c = ' ')) = (s.split (fun c => decide (c = ' '))).map sortWord := by
          simp [result]
          exact string_split_intercalate ((s.split (fun c => decide (c = ' '))).map sortWord)
        rw [h]
        simp [List.length_map]
      · -- main property for each word
        intro i hi
        let words := result.split (fun c => decide (c = ' '))
        let s_words := s.split (fun c => decide (c = ' '))
        have h_eq : words = s_words.map sortWord := by
          simp [words, result]
          exact string_split_intercalate (s_words.map sortWord)
        constructor
        · -- words[i]!.length = s_words[i]!.length
          rw [h_eq]
          simp [List.getElem_map]
          exact sortWord_length _
        · constructor
          · -- character membership and count preservation
            intro j hj
            have h_perm : (sortWord s_words[i]!).data ~ s_words[i]!.data := sortWord_data_perm s_words[i]!
            constructor
            · -- words[i]!.data[j]! ∈ s_words[i]!.data
              rw [h_eq] at hj
              simp [List.getElem_map] at hj
              rw [h_eq]
              simp [List.getElem_map]
              rw [mem_iff_of_perm h_perm]
              exact List.getElem_mem _ _ hj
            · constructor
              · -- s_words[i]!.data[j]! ∈ words[i]!.data
                rw [h_eq]
                simp [List.getElem_map]
                rw [← mem_iff_of_perm h_perm]
                exact List.getElem_mem _ _ hj
              · -- count preservation
                rw [h_eq]
                simp [List.getElem_map]
                rw [count_eq_of_perm h_perm]
                rw [← count_eq_of_perm h_perm]
                rfl
          · -- sorted property
            rw [h_eq]
            simp [List.getElem_map]
            exact sortWord_data_sorted s_words[i]!