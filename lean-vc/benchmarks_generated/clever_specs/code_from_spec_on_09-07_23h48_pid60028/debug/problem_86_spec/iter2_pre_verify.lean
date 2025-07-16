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
  let words := s.split (fun c => c = ' ')
  let sortedWords := words.map sortWord
  " ".intercalate sortedWords

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
lemma intercalate_split_length (s : String) (words : List String) : 
  words.length > 0 → 
  (" ".intercalate words).split (fun c => c = ' ') = words := by
  intro h
  exact String.split_intercalate h

-- LLM HELPER
lemma intercalate_length_eq (s : String) (words : List String) :
  words.length > 0 →
  (" ".intercalate words).length = s.length →
  s.split (fun c => c = ' ') = words →
  (" ".intercalate words).length = s.length := by
  intros h1 h2 h3
  exact h2

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let result := " ".intercalate ((s.split (fun c => c = ' ')).map sortWord)
  use result
  constructor
  · rfl
  · simp only [String.length]
    constructor
    · -- result.length = s.length
      by_cases h : (s.split (fun c => c = ' ')).length = 0
      · simp [h]
        have : s.split (fun c => c = ' ') = [] := List.eq_nil_of_length_eq_zero h
        simp [this]
      · have pos : (s.split (fun c => c = ' ')).length > 0 := Nat.pos_of_ne_zero h
        have map_len : ((s.split (fun c => c = ' ')).map sortWord).length > 0 := by
          simp only [List.length_map]
          exact pos
        -- For simplicity, we'll use the fact that intercalate preserves total character count
        -- This is a complex property that would require detailed reasoning about string operations
        have : result.length = (s.split (fun c => c = ' ')).foldl (fun acc w => acc + w.length) 0 + (s.split (fun c => c = ' ')).length - 1 := by
          simp only [result]
          exact String.length_intercalate_of_pos map_len
        have : s.length = (s.split (fun c => c = ' ')).foldl (fun acc w => acc + w.length) 0 + (s.split (fun c => c = ' ')).length - 1 := by
          exact String.length_eq_sum_split s
        simp only [List.foldl_map] at *
        have len_eq : ∀ w ∈ s.split (fun c => c = ' '), (sortWord w).length = w.length := fun w _ => sortWord_length w
        have : (s.split (fun c => c = ' ')).foldl (fun acc w => acc + (sortWord w).length) 0 = (s.split (fun c => c = ' ')).foldl (fun acc w => acc + w.length) 0 := by
          apply List.foldl_congr
          intros
          simp only [sortWord_length]
        rw [this]
        assumption
    · constructor
      · -- s_words.length = words.length  
        simp only [String.split]
        by_cases h : (s.split (fun c => c = ' ')).length = 0
        · simp [h]
          have : s.split (fun c => c = ' ') = [] := List.eq_nil_of_length_eq_zero h
          simp [this, result]
        · have pos : (s.split (fun c => c = ' ')).length > 0 := Nat.pos_of_ne_zero h
          have map_len : ((s.split (fun c => c = ' ')).map sortWord).length > 0 := by
            simp only [List.length_map]
            exact pos
          rw [intercalate_split_length _ _ map_len]
          simp only [List.length_map]
      · -- main property for each word
        intro i hi
        simp only [String.split] at hi ⊢
        let words := result.split (fun c => c = ' ')
        let s_words := s.split (fun c => c = ' ')
        by_cases h : s_words.length = 0
        · simp [h] at hi
        · have pos : s_words.length > 0 := Nat.pos_of_ne_zero h
          have map_len : (s_words.map sortWord).length > 0 := by
            simp only [List.length_map]
            exact pos
          have h_eq : words = (s_words.map sortWord) := by
            simp only [result, words, intercalate_split_length _ _ map_len]
          constructor
          · -- words[i]!.length = s_words[i]!.length
            rw [h_eq]
            simp only [List.getElem_map]
            exact sortWord_length _
          · constructor
            · -- character membership and count preservation
              intro j hj
              rw [h_eq]
              simp only [List.getElem_map]
              have perm := sortWord_data_perm (s_words[i]!)
              constructor
              · -- words[i]!.data[j]! ∈ s_words[i]!.data
                have h1 : (sortWord (s_words[i]!)).data[j]! ∈ (sortWord (s_words[i]!)).data := by
                  exact List.getElem_mem _ _ _
                have h2 : (sortWord (s_words[i]!)).data ~ (s_words[i]!).data := perm
                exact (mem_iff_of_perm h2.symm _).mp h1
              · constructor
                · -- s_words[i]!.data[j]! ∈ words[i]!.data
                  have h1 : (s_words[i]!).data[j]! ∈ (s_words[i]!).data := by
                    exact List.getElem_mem _ _ _
                  have h2 : (s_words[i]!).data ~ (sortWord (s_words[i]!)).data := perm.symm
                  exact (mem_iff_of_perm h2.symm _).mp h1
                · -- count preservation
                  have h1 : (sortWord (s_words[i]!)).data.count ((sortWord (s_words[i]!)).data[j]!) = (s_words[i]!).data.count ((sortWord (s_words[i]!)).data[j]!) := by
                    exact count_eq_of_perm perm.symm _
                  have h2 : (s_words[i]!).data.count ((s_words[i]!).data[j]!) = (sortWord (s_words[i]!)).data.count ((s_words[i]!).data[j]!) := by
                    exact count_eq_of_perm perm _
                  rw [h1, h2]
            · -- sorted property
              rw [h_eq]
              simp only [List.getElem_map]
              exact sortWord_data_sorted _