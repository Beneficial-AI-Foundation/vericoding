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
lemma String.join_cons (h : String) (t : List String) :
  String.join "" (h :: t) = h ++ String.join "" t := by
  simp [String.join]

-- LLM HELPER
lemma String.join_length (strings: List String) :
  (String.join "" strings).length = (strings.map String.length).sum := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih => 
    rw [String.join_cons, String.length_append, List.map_cons, List.sum_cons]
    exact ih

-- LLM HELPER
lemma List.getElem_take_succ (l : List α) (i : Nat) (h : i < l.length) :
  (l.take (i + 1))[i]? = l[i]? := by
  simp [List.getElem?_take]
  rw [if_pos (Nat.lt_succ_self i)]

-- LLM HELPER
lemma sum_take_succ (strings : List String) (i : Nat) (h : i < strings.length) :
  ((strings.take (i + 1)).map String.length).sum = 
  ((strings.take i).map String.length).sum + (strings[i]?.getD "").length := by
  have h_take : strings.take (i + 1) = strings.take i ++ [strings[i]?.getD ""] := by
    rw [List.take_succ_of_lt h]
    simp [List.getElem?_def]
    rw [List.get_cons_drop]
  rw [h_take, List.map_append, List.sum_append]
  simp

-- LLM HELPER
lemma String.join_take (strings : List String) (i : Nat) :
  String.join "" (strings.take i) = 
  ((String.join "" strings).toList.take ((strings.take i).map String.length).sum).asString := by
  induction i generalizing strings with
  | zero => simp [String.join, List.take]
  | succ j ih =>
    cases strings with
    | nil => simp [List.take]
    | cons h t =>
      simp [List.take_succ_cons, String.join_cons, List.map_cons, List.sum_cons]
      rw [String.append_eq_join, String.toList_append, List.take_append_eq_append_take]
      · rw [List.append_asString, ih]
        simp [String.toList_asString]
      · rw [String.join_length]
        exact le_self_add

-- LLM HELPER
lemma String.join_substring (strings: List String) (i: Nat) (hi: i < strings.length) :
  let result := String.join "" strings
  let string_in_result := strings[i]?.getD ""
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - string_in_result.length
  let corresponding_string_in_result := ((result.toList.take end_idx).drop start_idx).asString
  corresponding_string_in_result = string_in_result := by
  simp only [String.join]
  have h_eq : strings[i]?.getD "" = strings[i]?.getD "" := rfl
  rw [sum_take_succ strings i hi]
  simp [Nat.add_sub_cancel]
  rw [List.drop_take_comm]
  have h_join : String.join "" (strings.take i) = 
    ((String.join "" strings).toList.take ((strings.take i).map String.length).sum).asString := 
    String.join_take strings i
  rw [← h_join]
  rw [String.toList_asString]
  have h_split : String.join "" strings = String.join "" (strings.take i) ++ strings[i]?.getD "" ++ String.join "" (strings.drop (i + 1)) := by
    conv_lhs => rw [← List.take_append_drop i strings]
    rw [String.join_append]
    have h_cons : strings.drop i = strings[i]?.getD "" :: strings.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [List.getElem?_def]
    rw [h_cons, String.join_cons]
  rw [h_split, String.toList_append, String.toList_append]
  rw [List.take_append_eq_append_take]
  · simp [List.drop_append_eq_drop_drop]
    rw [List.take_left_of_le]
    simp [List.asString_toList]
    exact le_refl _
  · rw [String.join_length]
    exact le_self_add

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  simp [problem_spec, implementation]
  use String.join "" strings
  constructor
  · rfl
  · constructor
    · exact String.join_length strings
    · intro i hi
      exact String.join_substring strings i hi