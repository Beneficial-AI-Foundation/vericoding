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
(let string_in_result := strings[i]?.getD "";
let end_idx := ((strings.take (i + 1)).map (λ s => s.length)).sum;
let start_idx := end_idx - string_in_result.length;
let corresponding_string_in_result := ((result_chars.take end_idx).drop start_idx).asString;
corresponding_string_in_result = string_in_result);
-- program termination
∃ result, implementation strings = result ∧
spec result

def implementation (strings: List String) : String := 
  String.join "" strings

-- LLM HELPER
lemma String.join_nil (sep : String) : String.join sep [] = "" := by
  simp [String.join]

-- LLM HELPER
lemma String.join_cons (sep : String) (h : String) (t : List String) :
  String.join sep (h :: t) = h ++ String.join sep t := by
  simp [String.join]

-- LLM HELPER
lemma String.join_empty_length (strings: List String) :
  (String.join "" strings).length = (strings.map String.length).sum := by
  induction strings with
  | nil => simp [String.join_nil]
  | cons h t ih => 
    rw [String.join_cons, String.length_append, List.map_cons, List.sum_cons]
    exact ih

-- LLM HELPER
lemma sum_take_succ (strings : List String) (i : Nat) (h : i < strings.length) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings[i]?.getD "").length := by
  have h_take : strings.take (i + 1) = strings.take i ++ [strings[i]?.getD ""] := by
    rw [List.take_succ_of_lt h]
    simp [List.getElem?_def]
    congr 1
    rw [List.get_cons_drop]
  rw [h_take, List.map_append, List.sum_append]
  simp

-- LLM HELPER
lemma String.join_empty_concat (strings : List String) :
  String.join "" strings = (strings.map String.toList).join.asString := by
  induction strings with
  | nil => simp [String.join_nil]
  | cons h t ih =>
    rw [String.join_cons, List.map_cons, List.join_cons, List.append_asString]
    rw [String.toList_asString, ih]

-- LLM HELPER
lemma String.join_empty_substring (strings: List String) (i: Nat) (hi: i < strings.length) :
  let result := String.join "" strings
  let string_in_result := strings[i]?.getD ""
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - string_in_result.length
  let corresponding_string_in_result := ((result.toList.take end_idx).drop start_idx).asString
  corresponding_string_in_result = string_in_result := by
  simp only [String.join]
  rw [sum_take_succ strings i hi]
  simp [Nat.add_sub_cancel]
  rw [String.join_empty_concat]
  rw [String.toList_asString]
  have h_split : (strings.map String.toList).join = 
    (strings.take i).map String.toList).join ++ (strings[i]?.getD "").toList ++ ((strings.drop (i + 1)).map String.toList).join := by
    conv_lhs => rw [← List.take_append_drop i strings]
    rw [List.map_append, List.join_append]
    have h_cons : strings.drop i = strings[i]?.getD "" :: strings.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [List.getElem?_def]
    rw [h_cons, List.map_cons, List.join_cons]
  rw [h_split]
  rw [List.take_append_eq_append_take]
  · simp [List.drop_append_eq_drop_drop]
    rw [List.take_left_of_le (le_refl _)]
    rw [List.asString_toList]
  · exact le_self_add

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  simp [problem_spec, implementation]
  use String.join "" strings
  constructor
  · rfl
  · constructor
    · exact String.join_empty_length strings
    · intro i hi
      exact String.join_empty_substring strings i hi