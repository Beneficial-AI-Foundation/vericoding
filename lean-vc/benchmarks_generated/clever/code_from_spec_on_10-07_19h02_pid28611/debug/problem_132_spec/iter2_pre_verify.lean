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
lemma all_parens_implies_valid_chars (string : String) :
  string.toList.all (fun x => x = '(' ∨ x = ')') = true →
  string.toList.all (fun x => decide (x = '(' ∨ x = ')')) = true := by
  intro h
  simp [List.all_eq_true] at h ⊢
  exact h

-- LLM HELPER
lemma exists_valid_subsequence_iff (string : String) :
  has_valid_balanced_subsequence string = true ↔
  ∃ x : String, is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x := by
  constructor
  · intro h
    unfold has_valid_balanced_subsequence at h
    simp at h
    let chars := string.toList
    let parens := chars.filter (fun c => c = '(' ∨ c = ')')
    let all_subseqs := generate_all_subsequences parens
    have h_exists : ∃ subseq ∈ all_subseqs, 
      subseq.length ≥ 4 ∧ 
      balanced_paren_non_computable (String.mk subseq) '(' ')' ∧
      2 ≤ count_max_paren_depth (String.mk subseq) := by
      rw [List.any_eq_true] at h
      obtain ⟨subseq, h_mem, h_prop⟩ := h
      use subseq, h_mem
      by_cases h_len : subseq.length < 4
      · simp [h_len] at h_prop
      · simp [h_len] at h_prop
        push_neg at h_len
        exact ⟨h_len, h_prop⟩
    obtain ⟨subseq, h_mem, h_len, h_balanced, h_depth⟩ := h_exists
    use String.mk subseq
    constructor
    · have h_subseq_of_parens : is_subsequence subseq parens := by
        unfold generate_all_subsequences at h_mem
        induction parens generalizing subseq with
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
      have h_parens_subseq : is_subsequence parens chars := by
        unfold is_subsequence
        induction chars generalizing parens with
        | nil => 
          cases parens with
          | nil => simp
          | cons => simp [List.filter_nil] at *
        | cons h t ih =>
          simp [List.filter_cons]
          by_cases h_paren : h = '(' ∨ h = ')'
          · simp [h_paren]
            cases parens with
            | nil => simp
            | cons p_h p_t =>
              simp [List.filter_cons] at *
              by_cases h_eq : h = p_h
              · simp [h_eq]
                exact ih
              · simp [h_eq]
                exact ih
          · simp [h_paren]
            exact ih
      have h_trans : is_subsequence subseq chars := by
        unfold is_subsequence at h_subseq_of_parens h_parens_subseq ⊢
        induction chars generalizing subseq parens with
        | nil => 
          cases subseq with
          | nil => simp
          | cons => simp at h_len
        | cons h t ih =>
          cases subseq with
          | nil => simp
          | cons s_h s_t =>
            simp
            by_cases h_eq : s_h = h
            · simp [h_eq]
              exact ih
            · simp [h_eq]
              exact ih
      rw [← String.toList_mk]
      exact h_trans
    · exact ⟨h_balanced, h_depth⟩
  · intro h
    unfold has_valid_balanced_subsequence
    simp
    obtain ⟨x, h_subseq, h_balanced, h_depth⟩ := h
    let chars := string.toList
    let parens := chars.filter (fun c => c = '(' ∨ c = ')')
    let all_subseqs := generate_all_subsequences parens
    rw [List.any_eq_true]
    use x.toList
    constructor
    · have h_x_parens : x.toList.all (fun c => c = '(' ∨ c = ')') := by
        rw [List.all_eq_true]
        intro c h_mem
        have h_subseq_char : c ∈ chars := by
          unfold is_subsequence at h_subseq
          induction chars generalizing x.toList with
          | nil =>
            cases x.toList with
            | nil => simp at h_mem
            | cons => simp at h_subseq
          | cons h t ih =>
            cases x.toList with
            | nil => simp at h_mem
            | cons x_h x_t =>
              simp at h_subseq h_mem
              cases h_mem with
              | inl h_eq =>
                rw [← h_eq]
                by_cases h_match : x_h = h
                · simp [h_match] at h_subseq
                  simp [h_match]
                · simp [h_match] at h_subseq
                  exact ih h_subseq rfl
              | inr h_in_t =>
                by_cases h_match : x_h = h
                · simp [h_match] at h_subseq
                  exact ih h_subseq h_in_t
                · simp [h_match] at h_subseq
                  exact ih h_subseq h_in_t
        have h_char_filter : c ∈ parens := by
          simp [List.mem_filter]
          exact ⟨h_subseq_char, h_x_parens c h_mem⟩
        exact h_x_parens c h_mem
      have h_in_all_subseqs : x.toList ∈ all_subseqs := by
        unfold generate_all_subsequences
        induction parens generalizing x.toList with
        | nil =>
          cases x.toList with
          | nil => simp
          | cons => simp [List.all_eq_true] at h_x_parens
        | cons h t ih =>
          cases x.toList with
          | nil => simp
          | cons x_h x_t =>
            simp
            by_cases h_eq : x_h = h
            · right
              simp [List.mem_map]
              use x_t
              constructor
              · exact ih
              · simp [h_eq]
            · left
              exact ih
      exact h_in_all_subseqs
    · by_cases h_len : x.toList.length < 4
      · simp [h_len]
        have h_depth_ge_2 : 2 ≤ count_max_paren_depth x := h_depth
        unfold count_max_paren_depth at h_depth_ge_2
        simp at h_depth_ge_2
        have h_len_ge_4 : 4 ≤ x.toList.length := by
          by_contra h_not
          push_neg at h_not
          have h_len_lt_4 : x.toList.length < 4 := Nat.lt_of_not_ge h_not
          have h_balanced_needs_pairs : balanced_paren_non_computable x '(' ')' → 2 ≤ x.toList.length := by
            intro h_bal
            unfold balanced_paren_non_computable at h_bal
            simp at h_bal
            by_contra h_short
            push_neg at h_short
            interval_cases x.toList.length
            · simp [String.toList_eq] at h_bal h_depth_ge_2
              simp [count_max_paren_depth] at h_depth_ge_2
            · cases x.toList with
              | nil => simp at h_depth_ge_2
              | cons h t =>
                cases t with
                | nil => simp [count_max_paren_depth] at h_depth_ge_2
                | cons => simp at h_short
          have h_depth_needs_nesting : 2 ≤ count_max_paren_depth x → 4 ≤ x.toList.length := by
            intro h_d
            unfold count_max_paren_depth at h_d
            simp at h_d
            by_contra h_short
            push_neg at h_short
            interval_cases x.toList.length <;> simp [count_max_paren_depth] at h_d
          exact h_depth_needs_nesting h_depth_ge_2
        linarith
      · simp [h_len]
        rw [← String.toList_mk]
        exact ⟨h_balanced, h_depth⟩

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  use has_valid_balanced_subsequence string
  constructor
  · rfl
  · intro h
    rw [all_parens_implies_valid_chars string h]
    exact exists_valid_subsequence_iff string