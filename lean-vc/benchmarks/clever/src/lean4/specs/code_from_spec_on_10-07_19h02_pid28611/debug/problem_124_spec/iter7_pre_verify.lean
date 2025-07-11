import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(date: String) :=
-- spec
let spec (result: Bool) :=
  result = true ↔
    ∃ m1 m2 sep1 d1 d2 sep2 y1 y2 y3 y4 : Char,
    date = String.mk [m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4] ∧
    sep1 = '-' ∧ sep2 = '-' ∧
    [m1, m2, d1, d2, y1, y2, y3, y4].all Char.isDigit ∧
    let month := (String.mk [m1, m2]).toNat!;
    let day := (String.mk [d1, d2]).toNat!;
    1 ≤ month ∧ month ≤ 12 ∧
    (month ∈ ({4, 6, 9, 11}: List Nat) → 1 ≤ day ∧ day ≤ 30) ∧
    (month ∈ ({1, 3, 5, 7, 8, 10, 12}: List Nat) → 1 ≤ day ∧ day ≤ 31) ∧
    (month ∈ ({2}: List Nat) → 1 ≤ day ∧ day ≤ 29)
-- program terminates
∃ result, impl date = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def string_pos_2 : String.Pos := ⟨2⟩
-- LLM HELPER
def string_pos_5 : String.Pos := ⟨5⟩

def implementation (date: String) : Bool :=
  if date.length = 10 ∧ 
     date.get? string_pos_2 = some '-' ∧ 
     date.get? string_pos_5 = some '-' then
    let chars := date.data
    if chars.length = 10 ∧
       (chars.get? 0).isSome ∧ (chars.get? 0).get!.isDigit ∧ 
       (chars.get? 1).isSome ∧ (chars.get? 1).get!.isDigit ∧
       (chars.get? 3).isSome ∧ (chars.get? 3).get!.isDigit ∧ 
       (chars.get? 4).isSome ∧ (chars.get? 4).get!.isDigit ∧
       (chars.get? 6).isSome ∧ (chars.get? 6).get!.isDigit ∧ 
       (chars.get? 7).isSome ∧ (chars.get? 7).get!.isDigit ∧
       (chars.get? 8).isSome ∧ (chars.get? 8).get!.isDigit ∧ 
       (chars.get? 9).isSome ∧ (chars.get? 9).get!.isDigit then
      let month := (String.mk [chars[0]!, chars[1]!]).toNat!
      let day := (String.mk [chars[3]!, chars[4]!]).toNat!
      1 ≤ month ∧ month ≤ 12 ∧
      (month ∈ [4, 6, 9, 11] → 1 ≤ day ∧ day ≤ 30) ∧
      (month ∈ [1, 3, 5, 7, 8, 10, 12] → 1 ≤ day ∧ day ≤ 31) ∧
      (month = 2 → 1 ≤ day ∧ day ≤ 29)
    else
      false
  else
    false

-- LLM HELPER
lemma String.utf8_get_aux_eq (s : String) (idx : Nat) :
  s.get? ⟨idx⟩ = s.data.get? idx := by
  simp [String.get?, String.utf8GetAux?]

-- LLM HELPER
lemma list_get_bang_eq (l : List Char) (i : Nat) (h : i < l.length) :
  l.get! i = l[i]! := by
  simp [List.get!]
  rw [List.get?_eq_some]
  constructor
  · exact h
  · rfl

-- LLM HELPER
lemma string_mk_data_eq (chars : List Char) :
  (String.mk chars).data = chars := by
  simp [String.mk]

-- LLM HELPER
lemma string_from_ten_chars_eq (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Char) :
  String.mk [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] = 
  ⟨[c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]⟩ := by
  rfl

-- LLM HELPER
lemma string_length_eq_data_length (s : String) : s.length = s.data.length := by
  rfl

-- LLM HELPER
lemma list_get_option_some_iff (l : List α) (i : Nat) (x : α) :
  l.get? i = some x ↔ i < l.length ∧ l[i]! = x := by
  constructor
  · intro h
    have h1 : i < l.length := by
      by_contra h_not
      simp [List.get?_eq_none.mpr (Nat.le_of_not_gt h_not)] at h
    constructor
    · exact h1
    · rw [List.get!_eq_get]
      · simp [List.get?_eq_some] at h
        exact h.2
      · exact h1
  · intro ⟨h1, h2⟩
    rw [List.get?_eq_some]
    constructor
    · exact h1
    · rw [← List.get!_eq_get] at h2
      exact h2
      exact h1

theorem correctness
(date: String)
: problem_spec implementation date := by
  unfold problem_spec
  simp
  constructor
  · intro h
    simp [implementation] at h
    split_ifs at h with h1 h2
    · have h_len : date.length = 10 := h1.1
      have h_sep1 : date.get? string_pos_2 = some '-' := h1.2.1
      have h_sep2 : date.get? string_pos_5 = some '-' := h1.2.2
      have h_data_len : date.data.length = 10 := by
        rw [← string_length_eq_data_length]
        exact h_len
      
      -- Extract characters
      use date.data[0]!, date.data[1]!, date.data[2]!, date.data[3]!, date.data[4]!,
          date.data[5]!, date.data[6]!, date.data[7]!, date.data[8]!, date.data[9]!
      
      constructor
      · -- Show date equals the string construction
        ext i
        simp [String.mk]
        by_cases h_bound : i < 10
        · simp [h_bound, h_data_len]
        · simp [h_bound]
          have : i ≥ 10 := Nat.le_of_not_gt h_bound
          rw [List.get?_eq_none.mpr]
          rw [List.get?_eq_none.mpr]
          · rw [h_data_len]; exact this
          · rw [h_len]; exact this
      
      constructor
      · -- Show sep1 = '-'
        have : date.get? string_pos_2 = some date.data[2]! := by
          simp [String.utf8_get_aux_eq, string_pos_2]
          rw [list_get_option_some_iff]
          constructor
          · rw [h_data_len]; norm_num
          · rfl
        rw [h_sep1] at this
        injection this
      
      constructor  
      · -- Show sep2 = '-'
        have : date.get? string_pos_5 = some date.data[5]! := by
          simp [String.utf8_get_aux_eq, string_pos_5]
          rw [list_get_option_some_iff]
          constructor
          · rw [h_data_len]; norm_num
          · rfl
        rw [h_sep2] at this
        injection this
      
      constructor
      · -- Show all digits
        simp [List.all_eq_true]
        rw [string_length_eq_data_length] at h_len
        rw [h_len] at h2
        exact ⟨h2.2.1, h2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1,
               h2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.1,
               h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
      
      · -- Show month/day constraints
        simp [String.mk]
        rw [string_length_eq_data_length] at h_len
        rw [h_len] at h2
        exact h
    
    · simp at h
    · simp at h
  
  · intro h
    obtain ⟨m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4, h_eq, h_sep1, h_sep2, h_digits, h_valid⟩ := h
    simp [implementation]
    rw [h_eq]
    simp [string_mk_data_eq, h_sep1, h_sep2]
    simp [String.utf8_get_aux_eq, string_pos_2, string_pos_5]
    simp [List.all_eq_true] at h_digits
    simp [h_digits, String.mk]
    exact h_valid