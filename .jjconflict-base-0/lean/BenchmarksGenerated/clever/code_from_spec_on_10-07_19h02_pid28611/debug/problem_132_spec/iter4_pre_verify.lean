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
(string: String) :=
-- spec
let spec (result: Bool) :=
string.toList.all (fun x => x = '(' ∨ x = ')') →
result = true ↔
  ∃ x : String,
    is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x
-- program termination
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_subsequence (s t : List Char) : Bool :=
  match s, t with
  | [], _ => true
  | _, [] => false
  | h1::t1, h2::t2 => 
    if h1 = h2 then is_subsequence t1 t2
    else is_subsequence s t2

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open_char close_char : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (lst : List Char) (count : Int) : Bool :=
    match lst with
    | [] => count = 0
    | h::t => 
      if h = open_char then check_balance t (count + 1)
      else if h = close_char then 
        if count > 0 then check_balance t (count - 1)
        else false
      else check_balance t count
  check_balance chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.toList
  let rec helper (lst : List Char) (current_depth : Nat) (max_depth : Nat) : Nat :=
    match lst with
    | [] => max_depth
    | h::t =>
      if h = '(' then 
        let new_depth := current_depth + 1
        helper t new_depth (max new_depth max_depth)
      else if h = ')' then
        helper t (if current_depth > 0 then current_depth - 1 else 0) max_depth
      else
        helper t current_depth max_depth
  helper chars 0 0

-- LLM HELPER
def generate_all_subsequences (lst : List Char) : List (List Char) :=
  match lst with
  | [] => [[]]
  | h::t => 
    let rest := generate_all_subsequences t
    rest ++ (rest.map (fun subseq => h::subseq))

-- LLM HELPER
def has_valid_balanced_subsequence (s : String) : Bool :=
  let chars := s.toList
  let parens := chars.filter (fun c => c = '(' ∨ c = ')')
  let all_subseqs := generate_all_subsequences parens
  all_subseqs.any (fun subseq => 
    if subseq.length < 4 then false
    else
      let subseq_string := String.mk subseq
      balanced_paren_non_computable subseq_string '(' ')' ∧ 
      2 ≤ count_max_paren_depth subseq_string)

def implementation (lst: String) : Bool := has_valid_balanced_subsequence lst

-- LLM HELPER
lemma subsequence_of_subsequence_is_subsequence (a b c : List Char) :
  is_subsequence a b = true → is_subsequence b c = true → is_subsequence a c = true := by
  intro h1 h2
  induction c generalizing a b with
  | nil => 
    cases a with
    | nil => simp [is_subsequence]
    | cons => 
      cases b with
      | nil => simp [is_subsequence] at h1
      | cons => simp [is_subsequence] at h2
  | cons c_h c_t ih =>
    cases a with
    | nil => simp [is_subsequence]
    | cons a_h a_t =>
      cases b with
      | nil => simp [is_subsequence] at h1
      | cons b_h b_t =>
        simp [is_subsequence] at h1 h2 ⊢
        by_cases h_eq : a_h = c_h
        · simp [h_eq]
          by_cases h_b_eq : b_h = c_h
          · simp [h_b_eq] at h2
            by_cases h_a_b : a_h = b_h
            · simp [h_a_b] at h1
              exact ih h1 h2
            · simp [h_a_b] at h1
              exact ih h1 h2
          · simp [h_b_eq] at h2
            exact ih h1 h2
        · simp [h_eq]
          by_cases h_b_eq : b_h = c_h
          · simp [h_b_eq] at h2
            exact ih h1 h2
          · simp [h_b_eq] at h2
            exact ih h1 h2

-- LLM HELPER
lemma filter_subsequence (chars : List Char) (p : Char → Bool) :
  is_subsequence (chars.filter p) chars = true := by
  induction chars with
  | nil => simp [List.filter_nil, is_subsequence]
  | cons h t ih =>
    simp [List.filter_cons]
    by_cases h_p : p h
    · simp [h_p, is_subsequence]
      exact ih
    · simp [h_p, is_subsequence]
      exact ih

-- LLM HELPER
lemma generate_all_subsequences_correct (lst : List Char) (subseq : List Char) :
  subseq ∈ generate_all_subsequences lst → is_subsequence subseq lst = true := by
  intro h_mem
  induction lst generalizing subseq with
  | nil =>
    simp [generate_all_subsequences] at h_mem
    rw [h_mem]
    simp [is_subsequence]
  | cons h t ih =>
    simp [generate_all_subsequences] at h_mem
    cases h_mem with
    | inl h_in_rest =>
      have h_subseq := ih h_in_rest
      simp [is_subsequence]
      exact h_subseq
    | inr h_in_mapped =>
      simp [List.mem_map] at h_in_mapped
      obtain ⟨rest_subseq, h_rest_mem, h_eq⟩ := h_in_mapped
      rw [← h_eq]
      simp [is_subsequence]
      exact ih h_rest_mem

-- LLM HELPER
lemma string_toList_mk (chars : List Char) : (String.mk chars).toList = chars := by
  simp [String.toList, String.mk]

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  use has_valid_balanced_subsequence string
  constructor
  · rfl
  · intro h
    constructor
    · intro h_impl
      unfold has_valid_balanced_subsequence at h_impl
      simp at h_impl
      let chars := string.toList
      let parens := chars.filter (fun c => c = '(' ∨ c = ')')
      let all_subseqs := generate_all_subsequences parens
      rw [List.any_eq_true] at h_impl
      obtain ⟨subseq, h_mem, h_prop⟩ := h_impl
      by_cases h_len : subseq.length < 4
      · simp [h_len] at h_prop
      · simp [h_len] at h_prop
        push_neg at h_len
        use String.mk subseq
        constructor
        · have h_subseq_parens := generate_all_subsequences_correct parens subseq h_mem
          have h_parens_chars := filter_subsequence chars (fun c => c = '(' ∨ c = ')')
          have h_trans := subsequence_of_subsequence_is_subsequence subseq parens chars h_subseq_parens h_parens_chars
          rw [string_toList_mk]
          exact h_trans
        · rw [string_toList_mk]
          exact h_prop
    · intro h_exists
      obtain ⟨x, h_subseq, h_balanced, h_depth⟩ := h_exists
      unfold has_valid_balanced_subsequence
      simp
      let chars := string.toList
      let parens := chars.filter (fun c => c = '(' ∨ c = ')')
      let all_subseqs := generate_all_subsequences parens
      rw [List.any_eq_true]
      use x.toList
      constructor
      · have h_only_parens : x.toList.all (fun c => c = '(' ∨ c = ')') = true := by
          rw [List.all_eq_true]
          intro c h_in_c
          have h_c_in_string : c ∈ string.toList := by
            have h_is_subseq : is_subsequence x.toList string.toList = true := h_subseq
            induction string.toList generalizing x.toList with
            | nil => 
              cases x.toList with
              | nil => simp at h_in_c
              | cons => simp [is_subsequence] at h_is_subseq
            | cons s_h s_t ih =>
              cases x.toList with
              | nil => simp at h_in_c
              | cons x_h x_t =>
                simp [is_subsequence] at h_is_subseq
                cases h_in_c with
                | inl h_eq =>
                  rw [← h_eq]
                  by_cases h_match : x_h = s_h
                  · simp [h_match]
                    simp [h_match] at h_is_subseq
                  · simp [h_match] at h_is_subseq
                    exact ih h_is_subseq rfl
                | inr h_in_t =>
                  by_cases h_match : x_h = s_h
                  · simp [h_match] at h_is_subseq
                    exact ih h_is_subseq h_in_t
                  · simp [h_match] at h_is_subseq
                    exact ih h_is_subseq h_in_t
          rw [List.all_eq_true] at h
          exact h c h_c_in_string
        have h_subseq_parens : is_subsequence x.toList parens = true := by
          have h_parens_chars := filter_subsequence chars (fun c => c = '(' ∨ c = ')')
          have h_filtered : x.toList = x.toList.filter (fun c => c = '(' ∨ c = ')') := by
            rw [List.all_eq_true] at h_only_parens
            ext c
            simp [List.mem_filter]
            constructor
            · intro h_in_x
              exact ⟨h_in_x, h_only_parens c h_in_x⟩
            · intro h_filtered
              exact h_filtered.1
          rw [h_filtered]
          have h_chars_from_subseq : is_subsequence x.toList chars = true := h_subseq
          have h_filtered_subseq : is_subsequence (x.toList.filter (fun c => c = '(' ∨ c = ')')) (chars.filter (fun c => c = '(' ∨ c = ')')) = true := by
            rw [← h_filtered]
            have h_parens_def : parens = chars.filter (fun c => c = '(' ∨ c = ')') := rfl
            rw [← h_parens_def]
            exact subsequence_of_subsequence_is_subsequence x.toList chars parens h_chars_from_subseq h_parens_chars
          exact h_filtered_subseq
        use h_subseq_parens
      · by_cases h_len_check : x.toList.length < 4
        · simp [h_len_check]
          have h_min_len : 4 ≤ x.toList.length := by
            have h_depth_ge_2 : 2 ≤ count_max_paren_depth x := h_depth
            by_contra h_not_4
            push_neg at h_not_4
            have h_short : x.toList.length < 4 := h_not_4
            interval_cases x.toList.length
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
          linarith
        · simp [h_len_check]
          exact ⟨h_balanced, h_depth⟩