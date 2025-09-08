/- 
function_signature: "def valid_date(date: str) -> Bool"
docstring: |
    You have to write a function which validates a given date string and
    returns True if the date is valid otherwise False.
    The date is valid if all of the following rules are satisfied:
    1. The date string is not empty.
    2. The number of days is not less than 1 or higher than 31 days for months 1,3,5,7,8,10,12. And the number of days is not less than 1 or higher than 30 days for months 4,6,9,11. And, the number of days is not less than 1 or higher than 29 for the month 2.
    3. The months should not be less than 1 or higher than 12.
    4. The date should be in the format: mm-dd-yyyy
test_cases:
  - input: "03-11-2000"
    expected_output: True
  - input: "15-01-2012"
    expected_output: False
  - input: "04-0-2040"
    expected_output: False
  - input: "06-04-2020"
    expected_output: True
  - input: "06/04/2020"
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (date: String) : Bool :=
  if date.length ≠ 10 then false
  else
    let chars := date.toList
    if chars.length ≠ 10 then false
    else
      let m1 := chars[0]!
      let m2 := chars[1]!
      let sep1 := chars[2]!
      let d1 := chars[3]!
      let d2 := chars[4]!
      let sep2 := chars[5]!
      let y1 := chars[6]!
      let y2 := chars[7]!
      let y3 := chars[8]!
      let y4 := chars[9]!
      if sep1 ≠ '-' ∨ sep2 ≠ '-' then false
      else if ¬(m1.isDigit ∧ m2.isDigit ∧ d1.isDigit ∧ d2.isDigit ∧ y1.isDigit ∧ y2.isDigit ∧ y3.isDigit ∧ y4.isDigit) then false
      else
        let month := (String.mk [m1, m2]).toNat!
        let day := (String.mk [d1, d2]).toNat!
        if month < 1 ∨ month > 12 then false
        else if month ∈ [4, 6, 9, 11] then
          1 ≤ day ∧ day ≤ 30
        else if month ∈ [1, 3, 5, 7, 8, 10, 12] then
          1 ≤ day ∧ day ≤ 31
        else if month = 2 then
          1 ≤ day ∧ day ≤ 29
        else false

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
lemma string_length_eq_toList_length (s : String) : s.length = s.toList.length := by
  rw [String.length]

-- LLM HELPER
lemma list_all_isDigit_iff (cs : List Char) : cs.all Char.isDigit ↔ ∀ c ∈ cs, c.isDigit := by
  rw [List.all_eq_true]

-- LLM HELPER
lemma list_get_bang_eq (cs : List Char) (i : Nat) (h : i < cs.length) : 
  cs[i] = cs[i]! := by
  rw [List.getElem_eq_getElem!]

-- LLM HELPER
lemma list_get_valid (chars : List Char) (h : chars.length = 10) (i : Fin 10) :
  ↑i < chars.length := by
  rw [h]
  exact Fin.is_lt i

-- LLM HELPER
lemma month_partition (month : Nat) (h1 : 1 ≤ month) (h2 : month ≤ 12) :
  month ∈ [4, 6, 9, 11] ∨ month ∈ [1, 3, 5, 7, 8, 10, 12] ∨ month = 2 := by
  interval_cases month <;> simp

theorem correctness
(date: String)
: problem_spec implementation date := by
  unfold problem_spec
  simp only [implementation]
  by_cases h_len : date.length ≠ 10
  · simp [h_len]
    intro h_ex
    obtain ⟨m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4, h_eq, _, _, _, _, _, _, _⟩ := h_ex
    rw [h_eq] at h_len
    rw [String.length_mk] at h_len
    norm_num at h_len
  · simp [h_len]
    have h_len_eq : date.length = 10 := by omega
    have h_list_len : date.toList.length = 10 := by
      rw [← string_length_eq_toList_length]
      exact h_len_eq
    
    let chars := date.toList
    have h_chars_len : chars.length = 10 := h_list_len
    
    let m1 := chars[0]!
    let m2 := chars[1]!
    let sep1 := chars[2]!
    let d1 := chars[3]!
    let d2 := chars[4]!
    let sep2 := chars[5]!
    let y1 := chars[6]!
    let y2 := chars[7]!
    let y3 := chars[8]!
    let y4 := chars[9]!
    
    by_cases h_sep : sep1 ≠ '-' ∨ sep2 ≠ '-'
    · simp [h_sep]
      intro h_ex
      obtain ⟨m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4', h_eq, h_sep1, h_sep2, _, _, _, _, _⟩ := h_ex
      have h_chars_eq : chars = [m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4'] := by
        rw [← String.toList_mk] at h_eq
        rw [h_eq]
      cases h_sep with
      | inl h => 
        have : sep1 = sep1' := by
          rw [h_chars_eq]
          rfl
        rw [this] at h
        rw [h_sep1] at h
        simp at h
      | inr h =>
        have : sep2 = sep2' := by
          rw [h_chars_eq]
          rfl
        rw [this] at h
        rw [h_sep2] at h
        simp at h
    · simp [h_sep]
      have h_sep1_eq : sep1 = '-' := by
        push_neg at h_sep
        exact h_sep.1
      have h_sep2_eq : sep2 = '-' := by
        push_neg at h_sep
        exact h_sep.2
      
      by_cases h_digit : ¬(m1.isDigit ∧ m2.isDigit ∧ d1.isDigit ∧ d2.isDigit ∧ y1.isDigit ∧ y2.isDigit ∧ y3.isDigit ∧ y4.isDigit)
      · simp [h_digit]
        intro h_ex
        obtain ⟨m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4', h_eq, _, _, h_all_digit, _, _, _, _⟩ := h_ex
        have h_chars_eq : chars = [m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4'] := by
          rw [← String.toList_mk] at h_eq
          rw [h_eq]
        rw [list_all_isDigit_iff] at h_all_digit
        have h_digit_chars : m1.isDigit ∧ m2.isDigit ∧ d1.isDigit ∧ d2.isDigit ∧ y1.isDigit ∧ y2.isDigit ∧ y3.isDigit ∧ y4.isDigit := by
          rw [h_chars_eq]
          exact ⟨h_all_digit m1' (by simp), h_all_digit m2' (by simp), h_all_digit d1' (by simp), h_all_digit d2' (by simp),
                 h_all_digit y1' (by simp), h_all_digit y2' (by simp), h_all_digit y3' (by simp), h_all_digit y4' (by simp)⟩
        exact h_digit h_digit_chars
      · simp [h_digit]
        push_neg at h_digit
        
        let month := (String.mk [m1, m2]).toNat!
        let day := (String.mk [d1, d2]).toNat!
        
        by_cases h_month : month < 1 ∨ month > 12
        · simp [h_month]
          intro h_ex
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_month_bound, _, _, _⟩ := h_ex
          cases h_month with
          | inl h => omega
          | inr h => omega
        · simp [h_month]
          push_neg at h_month
          
          constructor
          · intro h_result
            use m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4
            constructor
            · have h_eq : date = String.mk (date.toList) := by rw [String.mk_toList]
              rw [h_eq]
              congr
              have h_chars_len' : chars.length = 10 := h_chars_len
              have h_chars : chars = [chars[0]!, chars[1]!, chars[2]!, chars[3]!, chars[4]!, chars[5]!, chars[6]!, chars[7]!, chars[8]!, chars[9]!] := by
                ext i
                fin_cases i <;> simp only <;> rw [list_get_bang_eq] <;> norm_num
              rw [h_chars]
              rfl
            constructor
            · exact h_sep1_eq
            constructor
            · exact h_sep2_eq
            constructor
            · rw [list_all_isDigit_iff]
              intro c hc
              simp at hc
              cases hc with
              | inl h => rw [h]; exact h_digit.1
              | inr h => cases h with
                | inl h => rw [h]; exact h_digit.2.1
                | inr h => cases h with
                  | inl h => rw [h]; exact h_digit.2.2.1
                  | inr h => cases h with
                    | inl h => rw [h]; exact h_digit.2.2.2.1
                    | inr h => cases h with
                      | inl h => rw [h]; exact h_digit.2.2.2.2.1
                      | inr h => cases h with
                        | inl h => rw [h]; exact h_digit.2.2.2.2.2.1
                        | inr h => cases h with
                          | inl h => rw [h]; exact h_digit.2.2.2.2.2.2.1
                          | inr h => rw [h]; exact h_digit.2.2.2.2.2.2.2
            constructor
            · exact h_month
            
            have h_month_cases := month_partition month h_month.1 h_month.2
            cases h_month_cases with
            | inl h_case1 =>
              constructor
              · intro h_in; exact h_result
              constructor
              · intro h_in; exfalso; interval_cases month <;> simp at h_case1 h_in
              · intro h_in; exfalso; interval_cases month <;> simp at h_case1 h_in
            | inr h_rest =>
              cases h_rest with
              | inl h_case2 =>
                constructor
                · intro h_in; exfalso; interval_cases month <;> simp at h_case2 h_in
                constructor
                · intro h_in; exact h_result
                · intro h_in; exfalso; interval_cases month <;> simp at h_case2 h_in
              | inr h_case3 =>
                constructor
                · intro h_in; exfalso; rw [h_case3] at h_in; simp at h_in
                constructor
                · intro h_in; exfalso; rw [h_case3] at h_in; simp at h_in
                · intro h_in; exact h_result
          
          · intro h_ex
            obtain ⟨m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4', h_eq, h_sep1', h_sep2', h_all_digit', month', day', h_month_bound', h_day1, h_day2, h_day3⟩ := h_ex
            
            have h_chars_match : [m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4] = [m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4'] := by
              have h_eq_chars : date.toList = [m1', m2', sep1', d1', d2', sep2', y1', y2', y3', y4'] := by
                rw [h_eq, String.toList_mk]
              have h_chars_def : chars = [m1, m2, sep1, d1, d2, sep2, y1, y2, y3, y4] := by
                ext i
                fin_cases i <;> simp only <;> rw [list_get_bang_eq] <;> norm_num
              rw [h_chars_def, ← h_eq_chars]
            
            have h_month_eq : month = month' := by
              congr 1
              rw [h_chars_match]
            
            have h_day_eq : day = day' := by
              congr 1
              rw [h_chars_match]
            
            rw [h_month_eq, h_day_eq] at *
            
            have h_month_cases := month_partition month' h_month_bound'.1 h_month_bound'.2
            cases h_month_cases with
            | inl h_case1 =>
              exact h_day1 h_case1
            | inr h_rest =>
              cases h_rest with
              | inl h_case2 =>
                exact h_day2 h_case2
              | inr h_case3 =>
                exact h_day3 (by simp [h_case3])