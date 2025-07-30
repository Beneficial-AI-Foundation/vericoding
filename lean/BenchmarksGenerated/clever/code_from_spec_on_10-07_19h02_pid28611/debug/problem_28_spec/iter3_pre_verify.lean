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
    simp [String.join]
    rw [String.length_append]
    rw [ih]
    simp [List.map_cons, List.sum_cons]

-- LLM HELPER
lemma string_join_toList (strings: List String) :
  (String.join strings).data = List.join (strings.map String.data) := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih =>
    simp [String.join, String.append_data, ih]
    simp [List.map_cons, List.join_cons]

-- LLM HELPER
lemma sum_take_map_length (strings: List String) (i : Nat) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings.get! i).length := by
  have h : i < strings.length ∨ i ≥ strings.length := Nat.lt_or_ge i strings.length
  cases h with
  | inl h_lt =>
    have take_succ : strings.take (i + 1) = strings.take i ++ [strings[i]] := by
      rw [List.take_succ_get _ h_lt]
    rw [take_succ]
    simp [List.map_append, List.sum_append]
    have : strings.get! i = strings[i] := by
      rw [List.get!_eq_getD, List.getD_eq_get]
      simp [h_lt]
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
  simp [List.get?_eq_some_iff.mpr h]

-- LLM HELPER
lemma join_get_property (strings: List String) (i : Nat) (h : i < strings.length) :
  let all_chars := List.join (strings.map String.data)
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - (strings.get! i).length
  ((all_chars.take end_idx).drop start_idx).asString = strings.get! i := by
  
  have h_eq : strings.get! i = strings[i] := by
    simp [List.get!_eq_getD, List.getD_eq_get, h]
  
  have start_eq : ((strings.take (i + 1)).map String.length).sum - (strings[i]).length = 
                  ((strings.take i).map String.length).sum := by
    rw [sum_take_map_length]
    simp [List.get!_eq_getD, List.getD_eq_get, h]
    omega
  
  have end_eq : ((strings.take (i + 1)).map String.length).sum = 
                ((strings.take i).map String.length).sum + (strings[i]).length := by
    rw [sum_take_map_length]
    simp [List.get!_eq_getD, List.getD_eq_get, h]
  
  -- Use the structure of joined lists
  have join_structure : 
    (List.join (strings.map String.data)).take ((strings.take (i + 1)).map String.length).sum =
    List.join ((strings.take (i + 1)).map String.data) := by
    rw [← List.map_take]
    apply List.take_join_of_length_eq
    simp [List.map_map]
    congr 1
    ext s
    simp [String.length_data]
    
  have join_drop_take :
    ((List.join (strings.map String.data)).take ((strings.take (i + 1)).map String.length).sum).drop 
    (((strings.take (i + 1)).map String.length).sum - (strings[i]).length) =
    (strings[i]).data := by
    rw [join_structure]
    rw [start_eq]
    have : List.join ((strings.take (i + 1)).map String.data) = 
           List.join ((strings.take i).map String.data) ++ (strings[i]).data := by
      rw [List.take_succ_get _ h, List.map_append, List.join_append]
      simp
    rw [this]
    rw [List.drop_append_of_le_length]
    simp
    rw [List.length_join]
    simp [List.map_map]
    simp [String.length_data]
    
  rw [h_eq]
  rw [← String.ext_iff]
  simp [String.data_asString]
  exact join_drop_take

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
      simp [String.length_data]
    · intro i hi
      simp
      rw [string_join_toList]
      rw [get_option_some_eq strings i hi]
      apply join_get_property
      exact hi