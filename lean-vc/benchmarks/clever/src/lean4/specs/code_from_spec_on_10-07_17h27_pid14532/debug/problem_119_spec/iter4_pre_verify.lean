import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def balanced_paren_non_computable (s : String) (open_char : Char) (close_char : Char) : Prop :=
  let chars := s.toList
  let rec helper (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        helper rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          helper rest (depth - 1)
        else
          false
      else
        helper rest depth
  helper chars 0 = true

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(l: List String) :=
-- spec
let spec (result : String) :=
  l.length = 2 →
  l[0]!.all (fun c => c = '(' ∨ c = ')') →
  l[1]!.all (fun c => c = '(' ∨ c = ')') →
  let res := (balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' ∨
            balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')')
  (res → result = "Yes") ∧
  (¬ res → result = "No")
-- program termination
∃ result,
  implementation l = result ∧
  spec result

-- LLM HELPER
def balanced_paren_computable (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec helper (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        helper rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          helper rest (depth - 1)
        else
          false
      else
        helper rest depth
  helper chars 0

def implementation (l: List String) : String := 
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    let concat1 := s1 ++ s2
    let concat2 := s2 ++ s1
    if balanced_paren_computable concat1 '(' ')' || balanced_paren_computable concat2 '(' ')' then
      "Yes"
    else
      "No"
  else
    "No"

-- LLM HELPER
theorem balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_non_computable s open_char close_char ↔ balanced_paren_computable s open_char close_char = true := by
  simp [balanced_paren_non_computable, balanced_paren_computable]

theorem correctness
(l: List String)
: problem_spec implementation l := by
  unfold problem_spec
  use (implementation l)
  constructor
  · rfl
  · intro h1 h2 h3
    rw [implementation]
    split_ifs with h
    · constructor
      · intro hyp
        simp only [Bool.or_eq_true]
        cases hyp with
        | inl h_left => 
          rw [balanced_paren_equiv] at h_left
          simp [h_left]
        | inr h_right =>
          rw [balanced_paren_equiv] at h_right
          simp [h_right]
      · intro hyp
        simp only [Bool.or_eq_true] at hyp
        push_neg at hyp
        cases hyp with
        | intro h_left h_right =>
          rw [←balanced_paren_equiv] at h_left h_right
          push_neg
          constructor
          · exact h_left
          · exact h_right
    · constructor
      · intro hyp
        cases hyp with
        | inl h_left => 
          have : l.length = 2 := h1
          contradiction
        | inr h_right =>
          have : l.length = 2 := h1
          contradiction
      · intro _
        rfl