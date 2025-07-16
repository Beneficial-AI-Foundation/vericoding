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
  unfold is_subsequence at h1 h2 ⊢
  induction c generalizing a b with
  | nil => 
    cases a with
    | nil => simp
    | cons => 
      cases b with
      | nil => simp at h1
      | cons => simp at h2
  | cons c_h c_t ih =>
    cases a with
    | nil => simp
    | cons a_h a_t =>
      cases b with
      | nil => simp at h1
      | cons b_h b_t =>
        simp at h1 h2 ⊢
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
      unfold has_valid_balanced_subsequence
      simp
      obtain ⟨x, h_subseq, h_balanced, h_depth⟩ := h_exists
      let chars := string.toList
      let parens := chars.filter (fun c => c = '(' ∨ c = ')')
      let all_subseqs := generate_all_subsequences parens
      rw [List.any_eq_true]
      use x.toList
      constructor
      · have h_x_only_parens : x.toList.all (fun c => c = '(' ∨ c = ')') := by
          rw [List.all_eq_true]
          intro c h_mem
          have h_depth_min : 2 ≤ count_max_paren_depth x := h_depth
          have h_balanced_true : balanced_paren_non_computable x '(' ')' = true := h_balanced
          unfold balanced_paren_non_computable at h_balanced_true
          simp at h_balanced_true
          by_contra h_not_paren
          push_neg at h_not_paren
          have h_not_open : c ≠ '(' := h_not_paren.1
          have h_not_close : c ≠ ')' := h_not_paren.2
          have h_in_string : c ∈ string.toList := by
            unfold is_subsequence at h_subseq
            induction string.toList generalizing x.toList with
            | nil =>
              cases x.toList with
              | nil => simp at h_mem
              | cons => simp at h_subseq
            | cons s_h s_t ih =>
              cases x.toList with
              | nil => simp at h_mem
              | cons x_h x_t =>
                simp at h_subseq h_mem
                cases h_mem with
                | inl h_eq =>
                  rw [← h_eq]
                  by_cases h_match : x_h = s_h
                  · simp [h_match] at h_subseq
                    simp [h_match]
                  · simp [h_match] at h_subseq
                    exact ih h_subseq rfl
                | inr h_in_t =>
                  by_cases h_match : x_h = s_h
                  · simp [h_match] at h_subseq
                    exact ih h_subseq h_in_t
                  · simp [h_match] at h_subseq
                    exact ih h_subseq h_in_t
          have h_string_all_parens : string.toList.all (fun x => x = '(' ∨ x = ')') = true := by
            simp [List.all_eq_true]
            exact h
          rw [List.all_eq_true] at h_string_all_parens
          have h_c_paren := h_string_all_parens c h_in_string
          exact h_not_paren h_c_paren
        have h_x_filtered : x.toList = parens.filter (fun c => c ∈ x.toList) := by
          ext c
          simp [List.mem_filter]
          constructor
          · intro h_in_x
            constructor
            · have h_in_chars : c ∈ chars := by
                unfold is_subsequence at h_subseq
                induction chars generalizing x.toList with
                | nil =>
                  cases x.toList with
                  | nil => simp at h_in_x
                  | cons => simp at h_subseq
                | cons h_c t_c ih =>
                  cases x.toList with
                  | nil => simp at h_in_x
                  | cons x_h x_t =>
                    simp at h_subseq h_in_x
                    cases h_in_x with
                    | inl h_eq =>
                      rw [← h_eq]
                      by_cases h_match : x_h = h_c
                      · simp [h_match] at h_subseq
                        simp [h_match]
                      · simp [h_match] at h_subseq
                        exact ih h_subseq rfl
                    | inr h_in_t =>
                      by_cases h_match : x_h = h_c
                      · simp [h_match] at h_subseq
                        exact ih h_subseq h_in_t
                      · simp [h_match] at h_subseq
                        exact ih h_subseq h_in_t
              simp [List.mem_filter]
              rw [List.all_eq_true] at h_x_only_parens
              exact ⟨h_in_chars, h_x_only_parens c h_in_x⟩
            · exact h_in_x
          · intro h_in_filtered
            exact h_in_filtered.2
        have h_subseq_parens : is_subsequence x.toList parens = true := by
          rw [h_x_filtered]
          exact filter_subsequence parens (fun c => c ∈ x.toList)
        have h_in_all_subseqs : x.toList ∈ all_subseqs := by
          unfold generate_all_subsequences
          induction parens generalizing x.toList with
          | nil =>
            simp [h_x_filtered]
            cases x.toList with
            | nil => simp
            | cons => simp [List.filter_nil] at h_x_filtered
          | cons p_h p_t ih =>
            simp
            by_cases h_in_x : p_h ∈ x.toList
            · right
              simp [List.mem_map]
              have h_x_tail : x.toList = p_h :: (x.toList.filter (fun c => c ≠ p_h)) ∨ 
                              ∃ prefix suffix, x.toList = prefix ++ [p_h] ++ suffix := by
                cases x.toList with
                | nil => simp at h_in_x
                | cons x_h x_t =>
                  by_cases h_eq : x_h = p_h
                  · left
                    simp [h_eq]
                    ext c
                    simp [List.mem_filter]
                    constructor
                    · intro h_in_t
                      constructor
                      · simp [h_in_t]
                      · rw [← h_eq]
                        exact h_in_t
                    · intro h_filtered
                      exact h_filtered.1
                  · right
                    use [], x_t
                    simp
                    have h_p_in_tail : p_h ∈ x_t := by
                      cases h_in_x with
                      | inl h_eq_contra => exact absurd h_eq_contra h_eq
                      | inr h_in_tail => exact h_in_tail
                    exact h_p_in_tail
              sorry
            · left
              exact ih
        exact h_in_all_subseqs
      · have h_len : x.toList.length ≥ 4 := by
          by_contra h_short
          push_neg at h_short
          have h_min_len : 4 ≤ x.toList.length := by
            have h_depth_ge_2 : 2 ≤ count_max_paren_depth x := h_depth
            have h_balanced_true : balanced_paren_non_computable x '(' ')' = true := h_balanced
            by_contra h_not_4
            push_neg at h_not_4
            interval_cases x.toList.length
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
            · simp [count_max_paren_depth] at h_depth_ge_2
          linarith
        by_cases h_len_check : x.toList.length < 4
        · simp [h_len_check]
          linarith
        · simp [h_len_check]
          exact ⟨h_balanced, h_depth⟩