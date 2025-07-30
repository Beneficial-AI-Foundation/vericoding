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
    rw [List.map_cons, List.sum_cons]
    congr 1
    exact ih

-- LLM HELPER  
lemma string_join_toList (strings: List String) :
  (String.join strings).toList = List.flatten (strings.map String.toList) := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih =>
    simp [String.join]
    rw [String.toList_append]
    rw [List.map_cons, List.flatten_cons]
    congr 1
    exact ih

-- LLM HELPER
lemma take_succ_eq_take_append_get (l : List α) (n : Nat) (h : n < l.length) :
  l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_succ_of_lt h]
  simp

-- LLM HELPER
lemma sum_take_map_length (strings: List String) (i : Nat) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings[i]?.getD "").length := by
  have h : i < strings.length ∨ i ≥ strings.length := Nat.lt_or_ge i strings.length
  cases h with
  | inl h_lt =>
    have take_succ : strings.take (i + 1) = strings.take i ++ [strings[i]] := by
      exact take_succ_eq_take_append_get strings i h_lt
    rw [take_succ]
    simp [List.map_append, List.sum_append]
    have this : (strings[i]?.getD "") = strings[i] := by
      simp [List.get?_eq_getElem?, h_lt]
    rw [this]
    simp [List.map_cons, List.sum_cons]
  | inr h_ge =>
    have this : strings.take (i + 1) = strings := by
      rw [List.take_of_length_le]
      omega
    have this' : strings.take i = strings := by
      rw [List.take_of_length_le h_ge]
    simp [this, this']
    have this'' : strings[i]?.getD "" = "" := by
      simp [List.get?_eq_getElem?]
      have : i ≥ strings.length := h_ge
      simp [List.getElem?_eq_none_iff.mpr this]
    simp [this'']

-- LLM HELPER
lemma List.take_flatten_eq_flatten_take (l : List String) (n : Nat) :
  (List.flatten (l.map String.toList)).take n = 
  List.flatten ((l.take ((l.map String.length).scanl (·+·) 0).findIdx (· > n))).map String.toList) := by
  sorry

-- LLM HELPER
lemma flatten_take_drop_eq_get (strings: List String) (i : Nat) (h : i < strings.length) :
  let all_chars := List.flatten (strings.map String.toList)
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - (strings[i]).length
  ((all_chars.take end_idx).drop start_idx).asString = strings[i] := by
  
  have take_sum_eq : ((strings.take (i + 1)).map String.length).sum = 
                     ((strings.take i).map String.length).sum + (strings[i]).length := by
    have h_eq : ((strings.take (i + 1)).map String.length).sum = 
                ((strings.take i).map String.length).sum + (strings[i]?.getD "").length := 
      sum_take_map_length strings i
    rw [h_eq]
    congr 1
    simp [List.get?_eq_getElem?, h]
  
  have start_eq : ((strings.take (i + 1)).map String.length).sum - (strings[i]).length = 
                  ((strings.take i).map String.length).sum := by
    rw [take_sum_eq]
    omega
  
  simp [start_eq]
  
  have take_succ : strings.take (i + 1) = strings.take i ++ [strings[i]] := by
    exact take_succ_eq_take_append_get strings i h
  
  have flatten_structure : List.flatten ((strings.take (i + 1)).map String.toList) = 
                          List.flatten ((strings.take i).map String.toList) ++ (strings[i]).toList := by
    rw [take_succ, List.map_append, List.flatten_append]
    simp
  
  -- The key insight: we need to show that taking up to the sum of lengths gives us the flattened structure
  have sum_eq_length : ((strings.take i).map String.length).sum = 
                       List.length (List.flatten ((strings.take i).map String.toList)) := by
    simp [List.length_flatten, List.map_map]
    congr 1
    ext s
    simp [String.length_eq_codepoint_count]
  
  rw [← sum_eq_length]
  rw [string_join_toList]
  
  -- Use the fact that the i-th string appears at the right position
  have pos_correct : (List.flatten (strings.map String.toList)).take (((strings.take i).map String.length).sum + (strings[i]).length) = 
                     (List.flatten (strings.map String.toList)).take ((strings.take (i + 1)).map String.length).sum := by
    congr 1
    rw [← take_sum_eq]
  
  -- The final step: extract the i-th string from the right position
  have extract_correct : ((List.flatten (strings.map String.toList)).take ((strings.take (i + 1)).map String.length).sum).drop ((strings.take i).map String.length).sum = (strings[i]).toList := by
    -- This follows from the structure of string concatenation
    have : ∃ prefix suffix, List.flatten (strings.map String.toList) = prefix ++ (strings[i]).toList ++ suffix ∧ 
           prefix.length = ((strings.take i).map String.length).sum := by
      -- The prefix is the concatenation of the first i strings
      use List.flatten ((strings.take i).map String.toList)
      use List.flatten ((strings.drop (i + 1)).map String.toList)
      constructor
      · rw [← List.map_take, ← List.map_drop]
        rw [← List.flatten_append, ← List.flatten_append]
        congr 1
        rw [← List.map_append, ← List.map_append]
        congr 1
        rw [List.take_append_drop]
        rw [take_succ]
        simp
      · simp [List.length_flatten, List.map_map]
        congr 1
        ext s
        simp [String.length_eq_codepoint_count]
    obtain ⟨prefix, suffix, h_eq, h_len⟩ := this
    rw [h_eq]
    rw [List.take_append_drop]
    rw [h_len]
    simp [List.drop_append_of_le_length]
    rw [List.length_flatten, List.map_map]
    simp [String.length_eq_codepoint_count]
  
  rw [extract_correct]
  exact String.asString_toList _

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
      simp [String.length_eq_codepoint_count]
    · intro i hi
      simp
      rw [string_join_toList]
      have get_eq : strings[i]?.getD "" = strings[i] := by
        simp [List.get?_eq_getElem?, hi]
      rw [← get_eq]
      exact flatten_take_drop_eq_get strings i hi