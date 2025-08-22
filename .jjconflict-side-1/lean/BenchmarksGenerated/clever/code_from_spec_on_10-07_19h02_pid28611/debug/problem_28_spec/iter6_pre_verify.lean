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
    simp [String.join, List.foldl_cons]
    rw [List.foldl_eq_foldr_of_comm_of_assoc]
    · simp [List.foldr_cons, String.length_append]
      rw [List.map_cons, List.sum_cons]
      congr 1
      exact ih
    · intros; rw [String.append_assoc]
    · intros; rw [String.append_assoc]

-- LLM HELPER
lemma string_join_toList (strings: List String) :
  (String.join strings).toList = List.flatten (strings.map String.toList) := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih =>
    simp [String.join, List.foldl_cons]
    rw [List.foldl_eq_foldr_of_comm_of_assoc]
    · simp [List.foldr_cons, String.toList_append]
      rw [List.map_cons, List.flatten_cons]
      congr 1
      exact ih
    · intros; rw [String.append_assoc]
    · intros; rw [String.append_assoc]

-- LLM HELPER
lemma take_succ_eq_take_append_get (l : List α) (n : Nat) (h : n < l.length) :
  l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_succ_of_length_succ]
  exact h

-- LLM HELPER
lemma sum_take_map_length (strings: List String) (i : Nat) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings.get! i).length := by
  have h : i < strings.length ∨ i ≥ strings.length := Nat.lt_or_ge i strings.length
  cases h with
  | inl h_lt =>
    have take_succ : strings.take (i + 1) = strings.take i ++ [strings[i]] := by
      exact take_succ_eq_take_append_get strings i h_lt
    rw [take_succ]
    simp [List.map_append, List.sum_append]
    have : strings.get! i = strings[i] := by
      simp [List.get!_eq_getD, List.getD_eq_getElem, h_lt]
    rw [this]
  | inr h_ge =>
    have : strings.take (i + 1) = strings := by
      rw [List.take_of_length_le]
      omega
    have : strings.take i = strings := by
      rw [List.take_of_length_le h_ge]
    simp [this]
    rw [List.get!_eq_getD]
    have : strings.getD i "" = "" := List.getD_eq_default _ h_ge
    simp [this]

-- LLM HELPER
lemma get_option_some_eq (strings: List String) (i : Nat) (h : i < strings.length) :
  strings[i]?.getD "" = strings[i] := by
  simp [List.get?_eq_getElem?, h]

-- LLM HELPER
lemma flatten_take_drop_eq_get (strings: List String) (i : Nat) (h : i < strings.length) :
  let all_chars := List.flatten (strings.map String.toList)
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - (strings[i]).length
  ((all_chars.take end_idx).drop start_idx).asString = strings[i] := by
  
  -- Key insight: the flattened structure preserves the substring boundaries
  have take_sum_eq : ((strings.take (i + 1)).map String.length).sum = 
                     ((strings.take i).map String.length).sum + (strings[i]).length := by
    rw [sum_take_map_length]
    simp [List.get!_eq_getD, List.getD_eq_getElem, h]
  
  have start_eq : ((strings.take (i + 1)).map String.length).sum - (strings[i]).length = 
                  ((strings.take i).map String.length).sum := by
    rw [take_sum_eq]
    omega
  
  rw [start_eq]
  
  -- The key property: taking from flattened list up to cumulative length
  have take_flatten_structure : 
    (List.flatten (strings.map String.toList)).take ((strings.take (i + 1)).map String.length).sum =
    List.flatten ((strings.take (i + 1)).map String.toList) := by
    rw [← List.map_take]
    have : ((strings.take (i + 1)).map String.length).sum = 
           ((strings.take (i + 1)).map String.toList).map List.length |>.sum := by
      simp [List.map_map]
      congr 1
      ext s
      simp [String.length_toList]
    rw [this]
    exact List.take_flatten_of_sum_map_length _ _
  
  have flatten_structure : List.flatten ((strings.take (i + 1)).map String.toList) = 
                          List.flatten ((strings.take i).map String.toList) ++ (strings[i]).toList := by
    have : strings.take (i + 1) = strings.take i ++ [strings[i]] := by
      exact take_succ_eq_take_append_get strings i h
    rw [this, List.map_append, List.flatten_append]
    simp
  
  rw [take_flatten_structure, flatten_structure]
  rw [List.drop_append_of_le_length]
  · simp
    rw [String.asString_toList]
  · simp [List.length_flatten, List.map_map]
    rw [List.sum_map_count_eq]
    simp [String.length_toList]

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  unfold problem_spec implementation
  use String.join strings
  constructor
  · rfl
  · constructor
    · rw [string_join_toList, string_join_length]
      simp [List.length_flatten, List.map_map]
      congr 1
      ext s
      simp [String.length_toList]
    · intro i hi
      simp
      rw [string_join_toList]
      rw [get_option_some_eq strings i hi]
      have : strings.get! i = strings[i] := by
        simp [List.get!_eq_getD, List.getD_eq_getElem, hi]
      rw [this]
      exact flatten_take_drop_eq_get strings i hi