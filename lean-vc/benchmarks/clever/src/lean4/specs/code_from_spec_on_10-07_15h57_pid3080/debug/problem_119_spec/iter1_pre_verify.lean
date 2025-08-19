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
  let rec count_balance (chars : List Char) (balance : Int) : Int :=
    match chars with
    | [] => balance
    | c :: rest =>
      if c = open_char then
        count_balance rest (balance + 1)
      else if c = close_char then
        if balance > 0 then
          count_balance rest (balance - 1)
        else
          -1000  -- Invalid state
      else
        count_balance rest balance
  let rec is_valid (chars : List Char) (balance : Int) : Bool :=
    match chars with
    | [] => balance = 0
    | c :: rest =>
      if c = open_char then
        is_valid rest (balance + 1)
      else if c = close_char then
        if balance > 0 then
          is_valid rest (balance - 1)
        else
          false
      else
        is_valid rest balance
  is_valid chars 0

-- LLM HELPER
def balanced_paren_check (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec is_valid (chars : List Char) (balance : Int) : Bool :=
    match chars with
    | [] => balance = 0
    | c :: rest =>
      if c = open_char then
        is_valid rest (balance + 1)
      else if c = close_char then
        if balance > 0 then
          is_valid rest (balance - 1)
        else
          false
      else
        is_valid rest balance
  is_valid chars 0

def implementation (l: List String) : String := 
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    let concat1 := s1 ++ s2
    let concat2 := s2 ++ s1
    if balanced_paren_check concat1 '(' ')' || balanced_paren_check concat2 '(' ')' then
      "Yes"
    else
      "No"
  else
    "No"

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_check s open_char close_char = true ↔ balanced_paren_non_computable s open_char close_char := by
  sorry

theorem correctness
(l: List String)
: problem_spec implementation l
:= by
  unfold problem_spec
  use implementation l
  constructor
  · rfl
  · intro h_len h_all1 h_all2
    simp [implementation]
    rw [h_len]
    simp
    constructor
    · intro h_res
      cases' h_res with h1 h2
      · simp
        rw [←balanced_paren_equiv] at h1
        simp [h1]
      · simp
        rw [←balanced_paren_equiv] at h2
        simp [h2]
    · intro h_not_res
      simp
      push_neg at h_not_res
      rw [←balanced_paren_equiv, ←balanced_paren_equiv] at h_not_res
      simp [h_not_res]