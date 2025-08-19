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
  ∃ (count : Nat), 
    (s.foldl (fun acc c => 
      if c = open_char then acc + 1 
      else if c = close_char then 
        if acc > 0 then acc - 1 else acc
      else acc) 0) = 0 ∧
    (∀ i : Nat, i < s.length → 
      (s.toList.take (i + 1).foldl (fun acc c => 
        if c = open_char then acc + 1 
        else if c = close_char then 
          if acc > 0 then acc - 1 else acc
        else acc) 0) ≥ 0)

-- LLM HELPER
def is_balanced_paren (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let (final_count, valid) := s.foldl (fun (acc, valid) c => 
    if c = open_char then (acc + 1, valid)
    else if c = close_char then 
      if acc > 0 then (acc - 1, valid) else (acc, false)
    else (acc, valid)) (0, true)
  valid && final_count = 0

def implementation (l: List String) : String := 
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    if s1.all (fun c => c = '(' ∨ c = ')') && s2.all (fun c => c = '(' ∨ c = ')') then
      if is_balanced_paren (s1 ++ s2) '(' ')' || is_balanced_paren (s2 ++ s1) '(' ')' then
        "Yes"
      else
        "No"
    else
      "No"
  else
    "No"

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open_char : Char) (close_char : Char) :
  balanced_paren_non_computable s open_char close_char ↔ is_balanced_paren s open_char close_char = true := by
  sorry

theorem correctness
(l: List String)
: problem_spec implementation l
:= by
  unfold problem_spec
  unfold implementation
  simp
  exists (if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    if s1.all (fun c => c = '(' ∨ c = ')') && s2.all (fun c => c = '(' ∨ c = ')') then
      if is_balanced_paren (s1 ++ s2) '(' ')' || is_balanced_paren (s2 ++ s1) '(' ')' then
        "Yes"
      else
        "No"
    else
      "No"
  else
    "No")
  constructor
  · rfl
  · intro h1 h2 h3
    simp [h1]
    split_ifs with h4
    · simp [h2, h3] at h4
      rw [balanced_paren_equiv, balanced_paren_equiv] at *
      simp [h4]
      constructor
      · intro h; rfl
      · intro h; rfl
    · simp [h2, h3] at h4
      rw [balanced_paren_equiv, balanced_paren_equiv] at *
      simp [h4]
      constructor
      · intro h; exfalso; exact h4 h
      · intro h; rfl