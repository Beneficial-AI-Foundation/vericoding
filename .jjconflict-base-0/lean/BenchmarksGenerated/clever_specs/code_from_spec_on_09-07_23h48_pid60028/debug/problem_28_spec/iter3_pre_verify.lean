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
  String.join strings ""

-- LLM HELPER
lemma String.join_length (strings: List String) :
  (String.join strings "").length = (strings.map String.length).sum := by
  induction strings with
  | nil => simp [String.join]
  | cons h t ih => 
    simp [String.join, String.length_append, ih]

-- LLM HELPER
lemma String.join_substring (strings: List String) (i: Nat) (hi: i < strings.length) :
  let result := String.join strings ""
  let string_in_result := strings[i]?.getD ""
  let end_idx := ((strings.take (i + 1)).map String.length).sum
  let start_idx := end_idx - string_in_result.length
  let corresponding_string_in_result := ((result.toList.take end_idx).drop start_idx).asString
  corresponding_string_in_result = string_in_result := by
  induction i generalizing strings with
  | zero =>
    cases strings with
    | nil => contradiction
    | cons h t =>
      simp [String.join, List.take, List.map]
      have h_eq : h.length - h.length = 0 := Nat.sub_self h.length
      simp [h_eq]
      rw [List.drop_zero, List.take_left_of_le]
      · simp [List.asString_toList]
      · simp [String.toList_append]
        exact le_self_add
  | succ j ih =>
    cases strings with
    | nil => contradiction
    | cons h t =>
      simp [String.join, List.take, List.map]
      have hj : j < t.length := by
        simp at hi
        exact Nat.lt_of_succ_lt_succ hi
      have h_rec := ih t hj
      simp [String.join] at h_rec
      rw [String.toList_append]
      simp [List.take_append, List.drop_append]
      have h_len : h.length ≤ ((t.take (j + 1)).map String.length).sum + h.length := 
        Nat.le_add_left h.length ((t.take (j + 1)).map String.length).sum
      rw [Nat.add_sub_cancel']
      simp [List.drop_take_comm]
      convert h_rec
      simp [List.asString_toList]

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  simp [problem_spec, implementation]
  use String.join strings ""
  constructor
  · rfl
  · constructor
    · exact String.join_length strings
    · intro i hi
      exact String.join_substring strings i hi