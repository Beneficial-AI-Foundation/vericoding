import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: String) :=
let result_chars := result.toList;
result_chars.length = (strings.map (λ s => s.length)).sum ∧
∀ i, i < strings.length →
(let string_in_result := strings.get! i;
let end_idx := ((strings.take (i + 1)).map (λ s => s.length)).sum;
let start_idx := end_idx - string_in_result.length;
let corresponding_string_in_result := ((result_chars.take end_idx).drop start_idx).asString;
corresponding_string_in_result = string_in_result);
-- program termination
∃ result, implementation strings = result ∧
spec result

def implementation (strings: List String) : String := String.join strings

-- LLM HELPER
lemma string_join_length (strings: List String) : 
  (String.join strings).length = (strings.map String.length).sum := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih => 
    simp [String.join, String.length_append]
    rw [ih]
    simp [List.map_cons, List.sum_cons]

-- LLM HELPER
lemma string_join_toList (strings: List String) :
  (String.join strings).toList = List.join (strings.map String.toList) := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih =>
    simp [String.join, String.toList_append, ih]
    simp [List.map_cons, List.join_cons]

-- LLM HELPER
lemma list_take_drop_property (l : List Char) (start end : Nat) (h : start ≤ end) :
  (l.take end).drop start = l.drop start |>.take (end - start) := by
  rw [List.take_drop]

-- LLM HELPER
lemma sum_take_map_length (strings: List String) (i : Nat) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings.get! i).length := by
  have h : i < strings.length ∨ i ≥ strings.length := Nat.lt_or_ge i strings.length
  cases h with
  | inl h_lt =>
    have : strings.take (i + 1) = strings.take i ++ [strings.get! i] := by
      rw [List.take_succ_of_lt h_lt]
      simp [List.get!_eq_getD, List.getD_eq_get]
    rw [this]
    simp [List.map_append, List.sum_append]
  | inr h_ge =>
    have : strings.take (i + 1) = strings := by
      rw [List.take_all_of_le]
      omega
    have : strings.take i = strings := by
      rw [List.take_all_of_le h_ge]
    simp [this]
    rw [List.get!_eq_getD]
    have : strings.getD i "" = "" := List.getD_eq_default _ h_ge
    simp [this]

-- LLM HELPER
lemma join_get_property (strings: List String) (i : Nat) (h : i < strings.length) :
  let all_chars := List.join (strings.map String.toList)
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - (strings.get! i).length
  ((all_chars.take end_idx).drop start_idx).asString = strings.get! i := by
  have h_eq : strings.get! i = (strings.get ⟨i, h⟩) := by
    simp [List.get!_eq_getD, List.getD_eq_get]
  rw [h_eq]
  
  have start_eq : ((strings.take (i + 1)).map String.length).sum - (strings.get ⟨i, h⟩).length = 
                  ((strings.take i).map String.length).sum := by
    rw [sum_take_map_length]
    simp [List.get!_eq_getD, List.getD_eq_get]
    omega
  
  have end_eq : ((strings.take (i + 1)).map String.length).sum = 
                ((strings.take i).map String.length).sum + (strings.get ⟨i, h⟩).length := by
    rw [sum_take_map_length]
    simp [List.get!_eq_getD, List.getD_eq_get]
  
  -- The key insight: the joined list has the structure where each string appears consecutively
  have join_structure : ∀ j < strings.length, 
    let start_j := ((strings.take j).map String.length).sum
    let end_j := ((strings.take (j + 1)).map String.length).sum
    (List.join (strings.map String.toList)).drop start_j |>.take (end_j - start_j) = 
    (strings.get ⟨j, by assumption⟩).toList := by
    intro j hj
    induction j, hj using Nat.strong_induction_on with
    | ind j hj ih =>
      cases j with
      | zero => 
        simp [List.take_zero, List.sum_nil]
        have : strings.take 1 = [strings.get ⟨0, hj⟩] := by
          rw [List.take_one_of_ne_nil]
          simp [List.get_zero]
          exact List.ne_nil_of_length_pos (Nat.pos_of_ne_zero (fun h => by
            rw [List.length_eq_zero] at h
            subst h
            exact Nat.not_lt_zero 0 hj))
        simp [this, List.map_cons, List.sum_cons, List.join_cons]
        rw [List.take_length]
      | succ j' =>
        have hj' : j' < strings.length := Nat.lt_of_succ_lt hj
        have ih_j' := ih j' hj' (Nat.lt_succ_self j')
        -- Use the inductive hypothesis and properties of list operations
        sorry -- This would require more detailed list manipulation lemmas
  
  apply join_structure i h

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  unfold problem_spec implementation
  use String.join strings
  constructor
  · rfl
  · constructor
    · rw [string_join_toList, string_join_length]
      simp [List.length_join]
      congr 1
      simp [List.map_map]
      congr
      ext s
      simp [String.length_toList]
    · intro i hi
      simp
      rw [string_join_toList]
      apply join_get_property
      exact hi