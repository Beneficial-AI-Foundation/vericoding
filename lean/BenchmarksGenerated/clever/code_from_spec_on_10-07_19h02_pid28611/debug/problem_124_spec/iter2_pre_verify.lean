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
      let month := (String.mk [(chars.get? 0).get!, (chars.get? 1).get!]).toNat!
      let day := (String.mk [(chars.get? 3).get!, (chars.get? 4).get!]).toNat!
      1 ≤ month ∧ month ≤ 12 ∧
      (month ∈ [4, 6, 9, 11] → 1 ≤ day ∧ day ≤ 30) ∧
      (month ∈ [1, 3, 5, 7, 8, 10, 12] → 1 ≤ day ∧ day ≤ 31) ∧
      (month = 2 → 1 ≤ day ∧ day ≤ 29)
    else
      false
  else
    false

theorem correctness
(date: String)
: problem_spec implementation date := by
  unfold problem_spec
  simp
  constructor
  · intro h
    if h1 : date.length = 10 ∧ date.get? string_pos_2 = some '-' ∧ date.get? string_pos_5 = some '-' then
      have len_eq : date.length = 10 := h1.1
      have sep1_eq : date.get? string_pos_2 = some '-' := h1.2.1
      have sep2_eq : date.get? string_pos_5 = some '-' := h1.2.2
      let chars := date.data
      have chars_len : chars.length = 10 := by
        rw [← String.length_data]
        exact len_eq
      if h2 : chars.length = 10 ∧
              (chars.get? 0).isSome ∧ (chars.get? 0).get!.isDigit ∧ 
              (chars.get? 1).isSome ∧ (chars.get? 1).get!.isDigit ∧
              (chars.get? 3).isSome ∧ (chars.get? 3).get!.isDigit ∧ 
              (chars.get? 4).isSome ∧ (chars.get? 4).get!.isDigit ∧
              (chars.get? 6).isSome ∧ (chars.get? 6).get!.isDigit ∧ 
              (chars.get? 7).isSome ∧ (chars.get? 7).get!.isDigit ∧
              (chars.get? 8).isSome ∧ (chars.get? 8).get!.isDigit ∧ 
              (chars.get? 9).isSome ∧ (chars.get? 9).get!.isDigit then
        simp [implementation, h1, h2]
        split_ifs with h3
        · use (chars.get? 0).get!, (chars.get? 1).get!, (chars.get? 2).get!, (chars.get? 3).get!, (chars.get? 4).get!, (chars.get? 5).get!, (chars.get? 6).get!, (chars.get? 7).get!, (chars.get? 8).get!, (chars.get? 9).get!
          constructor
          · rw [String.mk_eq_data]
            simp [chars_len]
            rfl
          constructor
          · have : (chars.get? 2).get! = '-' := by
              have h_get : date.get? string_pos_2 = some (chars.get? 2).get! := by
                rw [String.get?_eq_data_get?]
                simp [string_pos_2]
                rw [chars_len]
                simp
              rw [sep1_eq] at h_get
              simp at h_get
              exact h_get
            exact this
          constructor
          · have : (chars.get? 5).get! = '-' := by
              have h_get : date.get? string_pos_5 = some (chars.get? 5).get! := by
                rw [String.get?_eq_data_get?]
                simp [string_pos_5]
                rw [chars_len]
                simp
              rw [sep2_eq] at h_get
              simp at h_get
              exact h_get
            exact this
          constructor
          · simp [List.all_eq_true]
            exact ⟨h2.2.1, h2.2.2.2.1, h2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
          · simp
            exact h3
        · simp [implementation, h1, h2] at h
      else
        simp [implementation, h1, h2] at h
    else
      simp [implementation, h1] at h
  · intro h
    obtain ⟨m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4, h_eq, h_sep1, h_sep2, h_digits, h_valid⟩ := h
    simp [implementation]
    rw [h_eq]
    simp [h_sep1, h_sep2, string_pos_2, string_pos_5]
    simp [List.all_eq_true] at h_digits
    simp [h_digits]
    exact h_valid