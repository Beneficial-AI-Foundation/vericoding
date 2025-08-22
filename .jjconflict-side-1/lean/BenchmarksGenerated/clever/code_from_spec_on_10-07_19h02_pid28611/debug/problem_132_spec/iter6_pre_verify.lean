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
        · rw [String.toList_mk]
          sorry
        · rw [String.toList_mk]
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
      · sorry
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