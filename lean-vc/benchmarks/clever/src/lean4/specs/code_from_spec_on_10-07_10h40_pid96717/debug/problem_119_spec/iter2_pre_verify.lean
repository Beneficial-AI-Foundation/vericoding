import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def balanced_paren_non_computable (s : String) (open_char : Char) (close_char : Char) : Prop :=
  let chars := s.toList
  let rec balance_count (cs : List Char) (count : Int) : Option Int :=
    match cs with
    | [] => some count
    | c :: rest =>
      if c = open_char then
        balance_count rest (count + 1)
      else if c = close_char then
        if count > 0 then
          balance_count rest (count - 1)
        else
          none
      else
        balance_count rest count
  match balance_count chars 0 with
  | some 0 => True
  | _ => False

-- LLM HELPER
def is_balanced_paren (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec balance_count (cs : List Char) (count : Nat) : Option Nat :=
    match cs with
    | [] => some count
    | c :: rest =>
      if c = open_char then
        balance_count rest (count + 1)
      else if c = close_char then
        if count > 0 then
          balance_count rest (count - 1)
        else
          none
      else
        balance_count rest count
  match balance_count chars 0 with
  | some 0 => true
  | _ => false

def implementation (l: List String) : String :=
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    let concat1 := s1 ++ s2
    let concat2 := s2 ++ s1
    if is_balanced_paren concat1 '(' ')' || is_balanced_paren concat2 '(' ')' then
      "Yes"
    else
      "No"
  else
    "No"

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_non_computable s open_char close_char ↔ is_balanced_paren s open_char close_char = true := by
  constructor
  · intro h
    simp [balanced_paren_non_computable, is_balanced_paren] at h ⊢
    exact h
  · intro h
    simp [balanced_paren_non_computable, is_balanced_paren] at h ⊢
    exact h

theorem correctness
(l: List String)
: problem_spec implementation l
:= by
  simp [problem_spec]
  use implementation l
  simp [implementation]
  intro h_len h_all1 h_all2
  split_ifs with h
  · constructor
    · intro h_balanced
      cases h_balanced with
      | inl h1 => 
        rw [balanced_paren_equiv] at h1
        simp [h1]
      | inr h2 =>
        rw [balanced_paren_equiv] at h2
        simp [h2]
    · intro h_not_balanced
      push_neg at h_not_balanced
      have h1 : ¬is_balanced_paren (l[0]! ++ l[1]!) '(' ')' = true := by
        rw [← balanced_paren_equiv]
        exact h_not_balanced.1
      have h2 : ¬is_balanced_paren (l[1]! ++ l[0]!) '(' ')' = true := by
        rw [← balanced_paren_equiv]
        exact h_not_balanced.2
      simp [h1, h2]
  · constructor
    · intro h_balanced
      rfl
    · intro h_not_balanced
      rfl