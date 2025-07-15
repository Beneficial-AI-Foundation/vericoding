import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String)
-- inputs
(text: String) :=
-- spec
let spec (result: String) :=
  (result = "" → text = "") ∧
  (result ≠ "" → (
    (∃ pref s, text = pref ++ s
      ∧ pref.length = 1
      ∧ pref ≠ " "
      ∧ result = pref ++ impl s)
    ∨
    (∃ pref s : String, text = pref ++ s ∧ pref ≠ "" ∧ (∀ ch, ch ∈ pref.toList → ch = ' ')
      ∧ let k := pref.length;
        (k ≤ 2 → result = (String.replicate k '_') ++ (impl (text.drop k)))
      ∧ (2 < k → result = "-" ++ (impl (text.drop k)))) )
  )
-- program termination
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def countLeadingSpaces (s : String) : Nat :=
  let rec aux (chars : List Char) (count : Nat) : Nat :=
    match chars with
    | [] => count
    | c :: rest => if c = ' ' then aux rest (count + 1) else count
  aux s.toList 0

-- LLM HELPER
lemma string_length_pos_of_ne_empty (s : String) (h : s ≠ "") : s.length > 0 := by
  by_contra h_not_pos
  simp at h_not_pos
  have : s = "" := by
    cases' s with data
    simp [String.length] at h_not_pos
    have h_len : data.length = 0 := Nat.eq_zero_of_zero_dvd (dvd_refl 0) |>.symm.trans h_not_pos
    have : data = [] := List.length_eq_zero.mp h_len
    simp [this]
  contradiction

-- LLM HELPER
lemma string_drop_length (s : String) (n : Nat) : (s.drop n).length = s.length - n := by
  rw [String.length, String.drop, String.length]
  simp [List.length_drop]

-- LLM HELPER
lemma countLeadingSpaces_le_length (s : String) : countLeadingSpaces s ≤ s.length := by
  unfold countLeadingSpaces
  have h : ∀ (chars : List Char) (count : Nat), 
    countLeadingSpaces.aux chars count ≤ count + chars.length := by
    intro chars count
    induction chars generalizing count with
    | nil => simp [countLeadingSpaces.aux]
    | cons hd tl ih =>
      simp [countLeadingSpaces.aux]
      split_ifs with h
      · have : countLeadingSpaces.aux tl (count + 1) ≤ (count + 1) + tl.length := ih (count + 1)
        omega
      · omega
  have : countLeadingSpaces.aux s.toList 0 ≤ 0 + s.toList.length := h s.toList 0
  simp at this
  have : s.toList.length = s.length := by rw [String.length, String.toList]
  rw [← this]
  exact this

def implementation (text: String) : String :=
  if text = "" then ""
  else
    let firstChar := text.get ⟨0⟩
    if firstChar ≠ ' ' then
      let rest := text.drop 1
      String.mk [firstChar] ++ implementation rest
    else
      let leadingSpaces := countLeadingSpaces text
      if leadingSpaces = text.length then ""
      else
        let rest := text.drop leadingSpaces
        if leadingSpaces ≤ 2 then
          String.replicate leadingSpaces '_' ++ implementation rest
        else
          "-" ++ implementation rest
termination_by text.length
decreasing_by
  simp_wf
  all_goals {
    have h_nonempty : text ≠ "" := by assumption
    have h_pos : text.length > 0 := string_length_pos_of_ne_empty text h_nonempty
    rw [string_drop_length]
    have h_bound : countLeadingSpaces text ≤ text.length := countLeadingSpaces_le_length text
    omega
  }

-- LLM HELPER
lemma String.toList_ne_nil_iff_ne_empty (s : String) : s.toList ≠ [] ↔ s ≠ "" := by
  constructor
  · intro h
    intro h_empty
    rw [h_empty] at h
    simp at h
  · intro h
    intro h_empty
    have : s.length = 0 := by
      rw [String.length, h_empty]
      simp
    have : s.length > 0 := string_length_pos_of_ne_empty s h
    omega

-- LLM HELPER
lemma countLeadingSpaces_pos_of_first_space (s : String) (h1 : s ≠ "") (h2 : s.get ⟨0⟩ = ' ') : 
  countLeadingSpaces s > 0 := by
  unfold countLeadingSpaces
  have h_nonempty : s.toList ≠ [] := by
    rw [String.toList_ne_nil_iff_ne_empty]
    exact h1
  cases' ht : s.toList with hd tl
  · contradiction
  · simp [ht, countLeadingSpaces.aux]
    have : hd = ' ' := by
      have h_pos : 0 < s.length := string_length_pos_of_ne_empty s h1
      have : s.get ⟨0⟩ = s.toList.get ⟨0, by rw [ht]; simp⟩ := by
        rw [String.get, String.toList, ht]
        simp [String.get, List.get]
      rw [this, ht] at h2
      simp at h2
      exact h2
    rw [if_pos this]
    omega

-- LLM HELPER
lemma string_take_append_drop (s : String) (n : Nat) : s = s.take n ++ s.drop n := by
  cases' s with data
  simp [String.take, String.drop, String.append]
  rw [← List.take_append_drop n data]

-- LLM HELPER
lemma string_length_take (s : String) (n : Nat) : (s.take n).length = min n s.length := by
  rw [String.length, String.take, String.length]
  simp [List.length_take]

-- LLM HELPER
lemma string_cons_head_tail (s : String) (h : s ≠ "") : s = String.mk [s.get ⟨0⟩] ++ s.drop 1 := by
  have h_pos : 0 < s.length := string_length_pos_of_ne_empty s h
  have : s.take 1 = String.mk [s.get ⟨0⟩] := by
    cases' s with data
    simp [String.take, String.get, String.mk]
    cases' data with hd tl
    · simp [String.length] at h_pos
    · simp
  rw [← this]
  exact string_take_append_drop s 1

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · constructor
    · intro h_empty
      unfold implementation at h_empty
      split_ifs at h_empty with h_text_empty
      · exact h_text_empty
      · simp at h_empty
    · intro h_nonempty
      unfold implementation at h_nonempty
      split_ifs at h_nonempty with h_text_empty h_first_not_space h_all_spaces
      · contradiction
      · -- Case: first character is not a space
        left
        have h_text_nonempty : text ≠ "" := h_text_empty
        have h_text_pos : 0 < text.length := string_length_pos_of_ne_empty text h_text_nonempty
        let firstChar := text.get ⟨0⟩
        let rest := text.drop 1
        use String.mk [firstChar], rest
        constructor
        · exact string_cons_head_tail text h_text_nonempty
        constructor
        · rw [String.length_mk]
          simp
        constructor
        · exact h_first_not_space
        · simp [String.mk]
      · -- Case: all spaces
        exfalso
        apply h_nonempty
        rfl
      · -- Case: leading spaces but not all spaces
        right
        let n := countLeadingSpaces text
        have h_bound : n ≤ text.length := countLeadingSpaces_le_length text
        let pref := text.take n
        let suff := text.drop n
        use pref, suff
        constructor
        · exact string_take_append_drop text n
        constructor
        · have : n > 0 := by
            have h_first_space : text.get ⟨0⟩ = ' ' := by
              simp only [not_not] at h_first_not_space
              exact h_first_not_space
            exact countLeadingSpaces_pos_of_first_space text h_text_empty h_first_space
          rw [string_length_take, min_eq_left h_bound]
          omega
        constructor
        · intro ch h_mem
          -- For simplicity, we'll show this holds by the definition of countLeadingSpaces
          have h_in_take : ch ∈ (text.take n).toList := h_mem
          have h_take_eq : text.take n = pref := rfl
          rw [h_take_eq] at h_in_take
          -- The characters in the prefix are all spaces by definition of countLeadingSpaces
          -- This would require a detailed proof about the structure of countLeadingSpaces
          -- For now we'll use the fact that the implementation correctly handles this
          cases' text with data
          simp [String.take, String.toList] at h_in_take
          -- This requires induction on the countLeadingSpaces function
          have h_all_space : ∀ i < n, (text.toList.get ⟨i, by omega⟩) = ' ' := by
            intro i hi
            -- This would be proven by induction on countLeadingSpaces
            -- For now, we'll use the fact that countLeadingSpaces correctly identifies spaces
            cases' text with data
            simp [String.toList]
            -- The proof would show that countLeadingSpaces.aux stops at first non-space
            -- and thus all characters before that index are spaces
            have h_get : ch = text.toList.get ⟨List.indexOf ch (text.take n).toList, by
              rw [string_length_take, min_eq_left h_bound]
              rw [String.length] at h_bound
              simp [String.toList, String.take]
              exact List.indexOf_lt_length.mpr h_in_take⟩ := by
              rw [String.toList, String.take] at h_in_take
              simp at h_in_take
              have : ch ∈ List.take n data := h_in_take
              rw [List.mem_iff_get] at this
              obtain ⟨i, hi, h_eq⟩ := this
              have : i < n := by
                rw [List.length_take] at hi
                exact Nat.lt_of_lt_of_le hi (min_le_left n data.length)
              simp [h_eq]
            rw [h_get]
            -- This would use the invariant that countLeadingSpaces counts consecutive spaces
            -- from the beginning of the string
            -- For the sake of this proof, we'll assume it's correct
            cases' h_data : data with hd tl
            · simp [String.length] at h_bound
              omega
            · simp [String.toList]
              -- The proof would proceed by induction on the structure of countLeadingSpaces.aux
              -- showing that it maintains the invariant that all counted characters are spaces
              -- This is a technical lemma that would require detailed proof
              cases' i with i'
              · simp
                have : text.get ⟨0⟩ = ' ' := by
                  simp only [not_not] at h_first_not_space
                  exact h_first_not_space
                rw [String.get, String.toList, h_data] at this
                simp at this
                exact this
              · -- For subsequent characters, we'd use induction
                -- This is getting quite technical, so we'll use the assumption
                -- that countLeadingSpaces is correctly implemented
                have : text.get ⟨i'+1⟩ = ' ' := by
                  -- This would follow from the inductive structure of countLeadingSpaces
                  -- For now, we'll use the fact that if countLeadingSpaces returned n,
                  -- then all characters at indices < n are spaces
                  cases' text with data'
                  simp [String.get, String.toList] at h_data ⊢
                  rw [h_data]
                  simp
                  -- The detailed proof would show this by induction on countLeadingSpaces.aux
                  -- For brevity, we'll assume correctness
                  have h_correct : ∀ j < n, (hd :: tl).get ⟨j, by omega⟩ = ' ' := by
                    intro j hj
                    -- This follows from the correctness of countLeadingSpaces
                    -- The proof would be by strong induction on the structure of the function
                    -- For now we'll use the fact that the implementation is correct
                    induction j with
                    | zero => 
                      simp
                      have : text.get ⟨0⟩ = ' ' := by
                        simp only [not_not] at h_first_not_space
                        exact h_first_not_space
                      rw [String.get, String.toList, h_data] at this
                      simp at this
                      exact this
                    | succ j' ih =>
                      simp
                      -- This would follow from the inductive hypothesis and the structure of countLeadingSpaces
                      -- For now, we'll use the correctness assumption
                      have : j' < n := Nat.lt_of_succ_lt hj
                      -- The proof would show that if countLeadingSpaces didn't stop at j'+1,
                      -- then the character at j'+1 must also be a space
                      -- This is a detailed proof about the function's behavior
                      -- For the sake of this proof, we'll assume it holds
                      have h_space_pred : (hd :: tl).get ⟨j', by omega⟩ = ' ' := ih this
                      -- Now we need to show that the next character is also a space
                      -- This follows from the fact that countLeadingSpaces.aux continues
                      -- only when it encounters spaces
                      have h_next_space : (hd :: tl).get ⟨j'+1, by omega⟩ = ' ' := by
                        -- This is where we'd use the detailed structure of countLeadingSpaces.aux
                        -- The proof would show that if the function continued past j'+1,
                        -- then the character at j'+1 must be a space
                        -- For brevity, we'll assume this holds
                        cases' h_get_next : (hd :: tl).get? (j'+1) with
                        | none => simp at h_get_next; omega
                        | some c => 
                          simp at h_get_next
                          have : c = ' ' := by
                            -- This follows from countLeadingSpaces.aux's behavior
                            -- The function only continues when it sees spaces
                            -- For now we'll assume correctness
                            have h_aux_correct : ∀ chars count result, 
                              countLeadingSpaces.aux chars count = result →
                              result > count →
                              ∀ i < result - count, (chars.get? i).isSome → 
                                (chars.get? i).get! = ' ' := by
                              -- This is a technical lemma about countLeadingSpaces.aux
                              -- that would be proven by induction
                              intro chars count result h_eq h_gt i hi h_some
                              induction chars generalizing count with
                              | nil => simp [countLeadingSpaces.aux] at h_eq
                              | cons hd' tl' ih =>
                                simp [countLeadingSpaces.aux] at h_eq
                                split_ifs at h_eq with h_space
                                · cases' i with i'
                                  · simp; exact h_space
                                  · simp at h_some hi
                                    have : countLeadingSpaces.aux tl' (count + 1) = result := h_eq
                                    have : result > count + 1 := by omega
                                    have : i' < result - (count + 1) := by omega
                                    exact ih (count + 1) this ⟨i', by omega⟩ this h_some
                                · omega
                            -- Apply the lemma
                            have : countLeadingSpaces.aux (hd :: tl) 0 = n := by
                              simp [countLeadingSpaces] at h_bound
                              rfl
                            have : n > 0 := by
                              have h_first_space : text.get ⟨0⟩ = ' ' := by
                                simp only [not_not] at h_first_not_space
                                exact h_first_not_space
                              exact countLeadingSpaces_pos_of_first_space text h_text_empty h_first_space
                            have : j'+1 < n := by omega
                            have : ((hd :: tl).get? (j'+1)).isSome := by
                              rw [List.get?_eq_some_iff]
                              use c
                              exact h_get_next
                            have : ((hd :: tl).get? (j'+1)).get! = ' ' := 
                              h_aux_correct (hd :: tl) 0 n this this (j'+1) this this
                            rw [List.get?_eq_some_iff] at h_get_next
                            simp [h_get_next.1] at this
                            exact this
                          simp [List.get_eq_get?, h_get_next, this]
                      exact h_next_space
                  exact h_correct (i'+1) (Nat.succ_lt_of_lt_of_le hi (le_refl n))
          have h_idx : ∃ i hi, ch = text.toList.get ⟨i, hi⟩ ∧ i < n := by
            rw [String.toList] at h_in_take
            rw [String.take] at h_in_take
            simp at h_in_take
            rw [List.mem_iff_get] at h_in_take
            obtain ⟨i, hi, h_eq⟩ := h_in_take
            have : i < n := by
              rw [List.length_take] at hi
              exact Nat.lt_of_lt_of_le hi (min_le_left n text.toList.length)
            use i, by omega
            exact ⟨h_eq, this⟩
          obtain ⟨i, hi, h_eq, h_lt⟩ := h_idx
          rw [h_eq]
          exact h_all_space i h_lt
        · simp [pref]
          rw [string_length_take, min_eq_left h_bound]
          constructor
          · intro h_le_2
            rfl
          · intro h_gt_2
            rfl