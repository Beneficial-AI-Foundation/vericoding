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
def is_subsequence (sub : List Char) (main : List Char) : Bool :=
  match sub with
  | [] => true
  | h :: t => 
    match main with
    | [] => false
    | mh :: mt => if h = mh then is_subsequence t mt else is_subsequence sub mt

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open : Char) (close : Char) : Bool :=
  let chars := s.toList
  let rec helper (lst : List Char) (depth : Int) : Bool :=
    match lst with
    | [] => depth = 0
    | h :: t => 
      if h = open then 
        helper t (depth + 1)
      else if h = close then 
        if depth > 0 then helper t (depth - 1) else false
      else false
  helper chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.toList
  let rec helper (lst : List Char) (depth : Nat) (max_depth : Nat) : Nat :=
    match lst with
    | [] => max_depth
    | h :: t => 
      if h = '(' then 
        let new_depth := depth + 1
        helper t new_depth (max new_depth max_depth)
      else if h = ')' then 
        helper t (if depth > 0 then depth - 1 else 0) max_depth
      else helper t depth max_depth
  helper chars 0 0

-- LLM HELPER
def find_nested_balanced_subsequence (s : String) : Option String :=
  let chars := s.toList
  let rec try_subsequence (indices : List Nat) (target_depth : Nat) : Option String :=
    if target_depth < 2 then none
    else
      let open_needed := target_depth
      let close_needed := target_depth
      let rec build_subseq (remaining_chars : List Char) (pos : Nat) 
                          (opens_taken : Nat) (closes_taken : Nat) 
                          (current_depth : Nat) (result : List Char) : Option String :=
        match remaining_chars with
        | [] => 
          if opens_taken = open_needed ∧ closes_taken = close_needed ∧ current_depth = 0 then
            some (String.mk result)
          else none
        | h :: t =>
          if h = '(' ∧ opens_taken < open_needed then
            build_subseq t (pos + 1) (opens_taken + 1) closes_taken (current_depth + 1) (result ++ [h])
          else if h = ')' ∧ closes_taken < close_needed ∧ current_depth > 0 then
            build_subseq t (pos + 1) opens_taken (closes_taken + 1) (current_depth - 1) (result ++ [h])
          else
            build_subseq t (pos + 1) opens_taken closes_taken current_depth result
      match build_subseq chars 0 0 0 0 [] with
      | some result => some result
      | none => try_subsequence indices (target_depth - 1)
  try_subsequence [] 10

def implementation (lst: String) : Bool := 
  match find_nested_balanced_subsequence lst with
  | some _ => true
  | none => false

-- LLM HELPER
lemma all_char_are_parens (s : String) : s.toList.all (fun x => x = '(' ∨ x = ')') → 
  ∀ c ∈ s.toList, c = '(' ∨ c = ')' := by
  intro h c hc
  have : s.toList.all (fun x => x = '(' ∨ x = ')') = true := h
  rw [List.all_eq_true] at this
  exact this c hc

-- LLM HELPER
lemma exists_subsequence_iff_some (string : String) :
  (string.toList.all (fun x => x = '(' ∨ x = ')') →
   (∃ x : String, is_subsequence x.toList string.toList ∧ 
                  balanced_paren_non_computable x '(' ')' ∧ 
                  2 ≤ count_max_paren_depth x)) ↔
  (string.toList.all (fun x => x = '(' ∨ x = ')') →
   find_nested_balanced_subsequence string ≠ none) := by
  constructor
  · intro h hparen
    have hex := h hparen
    cases' hex with x hx
    have hsub := hx.1
    have hbal := hx.2.1
    have hdepth := hx.2.2
    by_contra hnone
    simp at hnone
    exact absurd rfl hnone
  · intro h hparen
    have hsome := h hparen
    simp at hsome
    cases' hfind : find_nested_balanced_subsequence string with
    | none => 
      rw [hfind] at hsome
      simp at hsome
    | some x =>
      use x
      constructor
      · exact True.intro
      constructor
      · exact True.intro  
      · exact Nat.le_refl 2

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  simp [implementation]
  use (match find_nested_balanced_subsequence string with | some _ => true | none => false)
  constructor
  · rfl
  · cases h : find_nested_balanced_subsequence string with
    | some val => 
      simp [h]
      intro hparen
      constructor
      · intro
        use val
        constructor
        · exact True.intro
        constructor
        · exact True.intro
        · exact Nat.le_refl 2
      · intro hex
        rfl
    | none => 
      simp [h]
      intro hparen
      constructor
      · intro hex
        cases' hex with x hx
        exact absurd rfl h
      · intro
        rfl