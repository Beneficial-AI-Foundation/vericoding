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

def implementation (date: String) : Bool :=
  if date.length = 10 ∧ 
     date.get? ⟨2⟩ = some '-' ∧ 
     date.get? ⟨5⟩ = some '-' then
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
lemma string_get_char_eq_data_get (s : String) (i : Nat) :
  i < s.length → s.get? ⟨i⟩ = s.data.get? i := by
  intro h
  simp [String.get?, String.utf8GetAux?]
  rw [String.length] at h
  simp [h]

-- LLM HELPER
lemma list_get_some_iff {α : Type*} (l : List α) (i : Nat) :
  (l.get? i).isSome ↔ i < l.length := by
  constructor
  · intro h
    by_contra h_not
    have h_ge : l.length ≤ i := Nat.le_of_not_gt h_not
    have h_none : l.get? i = none := List.get?_eq_none h_ge
    rw [h_none] at h
    simp at h
  · intro h
    rw [Option.isSome_iff_exists]
    exact List.get?_eq_some_iff.mpr ⟨l.get ⟨i, h⟩, List.get?_eq_get h⟩

-- LLM HELPER
lemma list_get_bang_eq_of_some {α : Type*} [Inhabited α] (l : List α) (i : Nat) :
  (l.get? i).isSome → l.get! i = (l.get? i).get! := by
  intro h
  simp [List.get!]
  cases h_eq : l.get? i with
  | none => simp at h
  | some a => simp [h_eq]

-- LLM HELPER
lemma string_mk_data_eq (chars : List Char) :
  (String.mk chars).data = chars := by
  simp [String.mk]

-- LLM HELPER
lemma string_length_eq_data_length (s : String) : s.length = s.data.length := by
  rfl

-- LLM HELPER
lemma list_get_bang_eq_get_of_valid {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
  l.get! i = l.get ⟨i, h⟩ := by
  rw [List.get!]
  simp [List.get?_eq_get h]

theorem correctness
(date: String)
: problem_spec implementation date := by
  unfold problem_spec
  use implementation date
  constructor
  · rfl
  · simp only [Bool.eq_true_iff]
    constructor
    · intro h
      simp [implementation] at h
      split_ifs at h with h1 h2
      · simp only [Bool.and_eq_true] at h1
        obtain ⟨h_len, h_sep1, h_sep2⟩ := h1
        simp only [Bool.and_eq_true] at h2
        obtain ⟨h_data_len, h_digits⟩ := h2
        
        -- Extract characters using the fact that they exist
        have h_len_data : date.data.length = 10 := by
          rw [← string_length_eq_data_length, h_len]
        
        -- Show all positions are valid
        have h0 : 0 < date.data.length := by rw [h_len_data]; norm_num
        have h1 : 1 < date.data.length := by rw [h_len_data]; norm_num
        have h2 : 2 < date.data.length := by rw [h_len_data]; norm_num
        have h3 : 3 < date.data.length := by rw [h_len_data]; norm_num
        have h4 : 4 < date.data.length := by rw [h_len_data]; norm_num
        have h5 : 5 < date.data.length := by rw [h_len_data]; norm_num
        have h6 : 6 < date.data.length := by rw [h_len_data]; norm_num
        have h7 : 7 < date.data.length := by rw [h_len_data]; norm_num
        have h8 : 8 < date.data.length := by rw [h_len_data]; norm_num
        have h9 : 9 < date.data.length := by rw [h_len_data]; norm_num
        
        use date.data.get ⟨0, h0⟩, date.data.get ⟨1, h1⟩, date.data.get ⟨2, h2⟩, 
            date.data.get ⟨3, h3⟩, date.data.get ⟨4, h4⟩, date.data.get ⟨5, h5⟩,
            date.data.get ⟨6, h6⟩, date.data.get ⟨7, h7⟩, date.data.get ⟨8, h8⟩, 
            date.data.get ⟨9, h9⟩
        
        constructor
        · -- Show date equals the string construction
          ext i
          simp [String.mk]
          by_cases h_bound : i < 10
          · simp [h_bound, h_len_data]
            interval_cases i <;> simp
          · simp [h_bound]
            have : i ≥ 10 := Nat.le_of_not_gt h_bound
            rw [List.get?_eq_none, List.get?_eq_none]
            · rw [h_len]; exact this
            · exact this
        
        constructor
        · -- Show sep1 = '-'
          have : date.get? ⟨2⟩ = some (date.data.get ⟨2, h2⟩) := by
            rw [string_get_char_eq_data_get, List.get?_eq_get]
            exact h2
          rw [h_sep1] at this
          injection this
        
        constructor  
        · -- Show sep2 = '-'
          have : date.get? ⟨5⟩ = some (date.data.get ⟨5, h5⟩) := by
            rw [string_get_char_eq_data_get, List.get?_eq_get]
            exact h5
          rw [h_sep2] at this
          injection this
        
        constructor
        · -- Show all digits
          simp [List.all_eq_true]
          simp only [Bool.and_eq_true] at h_digits
          obtain ⟨h_0_some, h_0_digit, h_1_some, h_1_digit, h_3_some, h_3_digit, 
                  h_4_some, h_4_digit, h_6_some, h_6_digit, h_7_some, h_7_digit,
                  h_8_some, h_8_digit, h_9_some, h_9_digit⟩ := h_digits
          simp [list_get_bang_eq_get_of_valid]
          exact ⟨h_0_digit, h_1_digit, h_3_digit, h_4_digit, h_6_digit, h_7_digit, h_8_digit, h_9_digit⟩
        
        · -- Show month/day constraints
          simp [String.mk]
          simp [list_get_bang_eq_get_of_valid]
          exact h
      · contradiction
      · contradiction
    
    · intro h
      obtain ⟨m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4, h_eq, h_sep1, h_sep2, h_digits, h_valid⟩ := h
      simp [implementation]
      rw [h_eq]
      simp [string_mk_data_eq, h_sep1, h_sep2]
      simp [string_get_char_eq_data_get, List.get?_cons_succ, List.get?_cons_zero]
      simp [List.all_eq_true] at h_digits
      simp [h_digits, String.mk]
      exact h_valid