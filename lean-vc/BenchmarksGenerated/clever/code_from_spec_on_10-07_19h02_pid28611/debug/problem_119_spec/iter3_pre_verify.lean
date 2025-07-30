import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def balanced_paren_non_computable (s : String) (open_char : Char) (close_char : Char) : Prop :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        check_balance rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          check_balance rest (depth - 1)
        else
          false
      else
        check_balance rest depth
  check_balance chars 0

-- LLM HELPER
def check_balanced_paren (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (depth : Nat) : Bool :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open_char then
        check_balance rest (depth + 1)
      else if c = close_char then
        if depth > 0 then
          check_balance rest (depth - 1)
        else
          false
      else
        check_balance rest depth
  check_balance chars 0

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_non_computable s open_char close_char ↔ check_balanced_paren s open_char close_char = true := by
  unfold balanced_paren_non_computable check_balanced_paren
  simp only [String.toList_toList]
  constructor
  · intro h
    sorry -- would need to prove equivalence of Int and Nat versions
  · intro h
    sorry -- would need to prove equivalence of Int and Nat versions

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

def implementation (l: List String) : String :=
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    if s1.all (fun c => c = '(' ∨ c = ')') ∧ s2.all (fun c => c = '(' ∨ c = ')') then
      let concat1 := s1 ++ s2
      let concat2 := s2 ++ s1
      if check_balanced_paren concat1 '(' ')' || check_balanced_paren concat2 '(' ')' then
        "Yes"
      else
        "No"
    else
      "No"
  else
    "No"

theorem correctness
(l: List String)
: problem_spec implementation l := by
  unfold problem_spec
  use implementation l
  constructor
  · rfl
  · intro h_len h_all1 h_all2
    simp [implementation, h_len, h_all1, h_all2]
    constructor
    · intro h_res
      cases h_res with
      | inl h1 =>
        have h1' : check_balanced_paren (l[0]! ++ l[1]!) '(' ')' = true := by
          rw [← balanced_paren_equiv]
          exact h1
        simp [h1']
      | inr h2 =>
        have h2' : check_balanced_paren (l[1]! ++ l[0]!) '(' ')' = true := by
          rw [← balanced_paren_equiv]
          exact h2
        simp [h2']
    · intro h_not_res
      by_contra h_contra
      apply h_not_res
      by_cases h1 : check_balanced_paren (l[0]! ++ l[1]!) '(' ')' = true
      · left
        rw [balanced_paren_equiv]
        exact h1
      · by_cases h2 : check_balanced_paren (l[1]! ++ l[0]!) '(' ')' = true
        · right
          rw [balanced_paren_equiv]
          exact h2
        · simp [h1, h2] at h_contra