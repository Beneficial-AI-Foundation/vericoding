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

-- LLM HELPER
lemma generate_all_subsequences_mem (lst : List Char) (subseq : List Char) :
  subseq ∈ generate_all_subsequences lst → 
  ∀ x ∈ subseq, x ∈ lst := by
  intro h x hx
  induction lst generalizing subseq with
  | nil => 
    simp [generate_all_subsequences] at h
    rw [h] at hx
    simp at hx
  | cons head tail ih =>
    simp [generate_all_subsequences] at h
    cases h with
    | inl h_left =>
      exact ih h_left x hx
    | inr h_right =>
      simp [List.mem_map] at h_right
      obtain ⟨rest_subseq, h_rest_mem, h_eq⟩ := h_right
      rw [←h_eq] at hx
      simp at hx
      cases hx with
      | inl h_head => 
        rw [h_head]
        simp
      | inr h_tail =>
        right
        exact ih h_rest_mem x h_tail

-- LLM HELPER
lemma subsequence_of_filter_is_subsequence (s : String) (subseq : List Char) :
  subseq ∈ generate_all_subsequences (s.toList.filter (fun c => c = '(' ∨ c = ')')) →
  is_subsequence subseq s.toList := by
  intro h
  have h_mem : ∀ x ∈ subseq, x ∈ s.toList.filter (fun c => c = '(' ∨ c = ')') := 
    generate_all_subsequences_mem _ _ h
  induction s.toList generalizing subseq with
  | nil =>
    simp [generate_all_subsequences] at h
    rw [h]
    simp [is_subsequence]
  | cons head tail ih =>
    cases subseq with
    | nil =>
      simp [is_subsequence]
    | cons subseq_head subseq_tail =>
      simp [is_subsequence]
      by_cases h_eq : subseq_head = head
      · simp [h_eq]
        apply ih
        have h_filter : subseq_tail ∈ generate_all_subsequences (tail.filter (fun c => c = '(' ∨ c = ')')) := by
          have h_orig : subseq_head :: subseq_tail ∈ generate_all_subsequences ((head :: tail).filter (fun c => c = '(' ∨ c = ')')) := h
          simp [List.filter] at h_orig
          by_cases h_paren : head = '(' ∨ head = ')'
          · simp [h_paren] at h_orig
            simp [generate_all_subsequences] at h_orig
            cases h_orig with
            | inl h_left =>
              have h_empty : subseq_head :: subseq_tail = [] := by
                simp [generate_all_subsequences] at h_left
                exact h_left
              simp at h_empty
            | inr h_right =>
              simp [List.mem_map] at h_right
              obtain ⟨rest, h_rest_mem, h_rest_eq⟩ := h_right
              have h_cons : subseq_head :: subseq_tail = head :: rest := h_rest_eq
              simp at h_cons
              rw [←h_cons.2]
              exact h_rest_mem
          · simp [h_paren] at h_orig
            exact h_orig
        exact h_filter
      · simp [h_eq]
        apply ih
        have h_filter : subseq_head :: subseq_tail ∈ generate_all_subsequences (tail.filter (fun c => c = '(' ∨ c = ')')) := by
          have h_orig : subseq_head :: subseq_tail ∈ generate_all_subsequences ((head :: tail).filter (fun c => c = '(' ∨ c = ')')) := h
          simp [List.filter] at h_orig
          by_cases h_paren : head = '(' ∨ head = ')'
          · simp [h_paren] at h_orig
            simp [generate_all_subsequences] at h_orig
            cases h_orig with
            | inl h_left =>
              exact h_left
            | inr h_right =>
              simp [List.mem_map] at h_right
              obtain ⟨rest, h_rest_mem, h_rest_eq⟩ := h_right
              have h_cons : subseq_head :: subseq_tail = head :: rest := h_rest_eq
              simp at h_cons
              rw [h_cons.1] at h_eq
              contradiction
          · simp [h_paren] at h_orig
            exact h_orig
        exact h_filter

-- LLM HELPER
lemma exists_subsequence_from_valid (s : String) (subseq : List Char) :
  subseq ∈ generate_all_subsequences (s.toList.filter (fun c => c = '(' ∨ c = ')')) →
  ∃ x : String, is_subsequence x.toList s.toList ∧ x.toList = subseq := by
  intro h
  use String.mk subseq
  constructor
  · simp
    exact subsequence_of_filter_is_subsequence s subseq h
  · simp

-- LLM HELPER
lemma valid_subseq_in_generated (s : String) (x : String) :
  is_subsequence x.toList s.toList →
  (∀ c ∈ x.toList, c = '(' ∨ c = ')') →
  x.toList ∈ generate_all_subsequences (s.toList.filter (fun c => c = '(' ∨ c = ')')) := by
  intro h_subseq h_parens
  induction s.toList generalizing x with
  | nil =>
    simp [is_subsequence] at h_subseq
    cases x.toList with
    | nil =>
      simp [generate_all_subsequences]
    | cons head tail =>
      simp at h_subseq
  | cons head tail ih =>
    simp [List.filter]
    by_cases h_paren : head = '(' ∨ head = ')'
    · simp [h_paren, generate_all_subsequences]
      cases x.toList with
      | nil =>
        left
        simp [generate_all_subsequences]
      | cons x_head x_tail =>
        simp [is_subsequence] at h_subseq
        cases h_subseq with
        | inl h_match =>
          obtain ⟨h_eq, h_rest⟩ := h_match
          right
          simp [List.mem_map]
          use x_tail
          constructor
          · apply ih
            exact h_rest
            intro c hc
            exact h_parens c (by simp; right; exact hc)
          · simp [h_eq]
        | inr h_skip =>
          left
          apply ih
          exact h_skip
          exact h_parens
    · simp [h_paren]
      apply ih
      simp [is_subsequence] at h_subseq
      cases x.toList with
      | nil =>
        simp [is_subsequence]
      | cons x_head x_tail =>
        simp [is_subsequence] at h_subseq
        cases h_subseq with
        | inl h_match =>
          obtain ⟨h_eq, h_rest⟩ := h_match
          rw [h_eq] at h_paren
          have h_x_paren : x_head = '(' ∨ x_head = ')' := h_parens x_head (by simp)
          contradiction
        | inr h_skip =>
          exact h_skip
      exact h_parens

-- LLM HELPER
lemma subsequence_mem_implies_in_string (s : String) (x : String) (c : Char) :
  is_subsequence x.toList s.toList →
  c ∈ x.toList →
  c ∈ s.toList := by
  intro h_sub hc
  induction s.toList generalizing x with
  | nil =>
    simp [is_subsequence] at h_sub
    cases x.toList with
    | nil => simp at hc
    | cons => simp at h_sub
  | cons head tail ih =>
    simp [is_subsequence] at h_sub
    cases x.toList with
    | nil => simp at hc
    | cons x_head x_tail =>
      simp [is_subsequence] at h_sub
      cases h_sub with
      | inl h_match =>
        obtain ⟨h_eq, h_rest⟩ := h_match
        simp at hc
        cases hc with
        | inl h_first =>
          rw [h_first, h_eq]
          simp
        | inr h_rest_mem =>
          right
          exact ih h_rest h_rest_mem
      | inr h_skip =>
        right
        exact ih h_skip hc

-- LLM HELPER
lemma depth_implies_length (x : String) :
  2 ≤ count_max_paren_depth x → 4 ≤ x.toList.length := by
  intro h_depth
  by_contra h_not_4
  push_neg at h_not_4
  have h_short : x.toList.length < 4 := h_not_4
  interval_cases x.toList.length
  · simp [count_max_paren_depth] at h_depth
  · simp [count_max_paren_depth] at h_depth
  · simp [count_max_paren_depth] at h_depth
  · simp [count_max_paren_depth] at h_depth

def implementation (lst: String) : Bool := has_valid_balanced_subsequence lst

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
        obtain ⟨x, h_subseq, h_eq⟩ := exists_subsequence_from_valid string subseq h_mem
        use x
        constructor
        · exact h_subseq
        · rw [←h_eq]
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
      · have h_all_parens : ∀ c ∈ x.toList, c = '(' ∨ c = ')' := by
          intro c hc
          have h_all : string.toList.all (fun x => x = '(' ∨ x = ')') := by
            exact h
          rw [List.all_eq_true] at h_all
          have h_in : c ∈ string.toList := subsequence_mem_implies_in_string string x c h_subseq hc
          exact h_all c h_in
        exact valid_subseq_in_generated string x h_subseq h_all_parens
      · have h_min_len : 4 ≤ x.toList.length := depth_implies_length x h_depth
        have h_len_check : ¬(x.toList.length < 4) := by linarith
        simp [h_len_check]
        exact ⟨h_balanced, h_depth⟩