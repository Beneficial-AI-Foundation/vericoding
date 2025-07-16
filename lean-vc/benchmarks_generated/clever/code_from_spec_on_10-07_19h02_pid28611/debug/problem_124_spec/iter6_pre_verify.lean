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
lemma String.length_data_eq (s : String) : s.data.length = s.length := by
  rfl

-- LLM HELPER
lemma string_get_pos_2 (s : String) (h : s.length = 10) : 
  s.get? string_pos_2 = some s.data[2]! := by
  simp [String.get?, string_pos_2]
  rw [h]
  simp

-- LLM HELPER
lemma string_get_pos_5 (s : String) (h : s.length = 10) : 
  s.get? string_pos_5 = some s.data[5]! := by
  simp [String.get?, string_pos_5]
  rw [h]
  simp

-- LLM HELPER
lemma string_mk_ten_chars (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Char) :
  (String.mk [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]).data = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] := by
  simp [String.mk]

-- LLM HELPER
lemma extract_chars_from_valid_date (date : String) 
  (h_len : date.length = 10) 
  (h_sep1 : date.get? string_pos_2 = some '-') 
  (h_sep2 : date.get? string_pos_5 = some '-') :
  ∃ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Char,
    date = String.mk [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] ∧ 
    c2 = '-' ∧ c5 = '-' ∧
    date.data = [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9] := by
  have h_data_len : date.data.length = 10 := by rw [← String.length_data_eq, h_len]
  use date.data[0]!, date.data[1]!, date.data[2]!, date.data[3]!, date.data[4]!, 
      date.data[5]!, date.data[6]!, date.data[7]!, date.data[8]!, date.data[9]!
  constructor
  · ext n
    simp [String.mk]
    by_cases h : n < 10
    · simp [h, h_data_len]
    · simp [h]
      have : n ≥ 10 := Nat.le_of_not_gt h
      rw [List.get?_eq_none.mpr]
      rw [List.get?_eq_none.mpr]
      · rw [h_data_len]
        exact this
      · rw [h_len]
        exact this
  constructor
  · have : date.get? string_pos_2 = some date.data[2]! := string_get_pos_2 date h_len
    rw [h_sep1] at this
    injection this
  constructor
  · have : date.get? string_pos_5 = some date.data[5]! := string_get_pos_5 date h_len
    rw [h_sep2] at this
    injection this
  · rfl

theorem correctness
(date: String)
: problem_spec implementation date := by
  unfold problem_spec
  simp
  constructor
  · intro h
    simp [implementation] at h
    split_ifs at h with h1 h2
    · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, h_eq, h_sep1, h_sep2, h_data⟩ := 
        extract_chars_from_valid_date date h1.1 h1.2.1 h1.2.2
      use c0, c1, c2, c3, c4, c5, c6, c7, c8, c9
      constructor
      · exact h_eq
      constructor
      · exact h_sep1
      constructor
      · exact h_sep2
      constructor
      · simp [List.all_eq_true]
        rw [h_data] at h2
        simp at h2
        exact ⟨h2.2.1, h2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1, 
               h2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.1, 
               h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
      · simp [String.mk]
        rw [h_data]
        simp at h
        exact h
    · simp at h
    · simp at h
  · intro h
    obtain ⟨m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4, h_eq, h_sep1, h_sep2, h_digits, h_valid⟩ := h
    simp [implementation]
    rw [h_eq]
    simp [h_sep1, h_sep2, string_pos_2, string_pos_5, string_mk_ten_chars]
    simp [List.all_eq_true] at h_digits
    simp [h_digits]
    exact h_valid