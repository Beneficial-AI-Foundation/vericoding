import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(brackets: String) :=
-- spec
let spec (result: Bool) :=
  brackets.data.all (fun c => c = '<' ∨ c = '>') →
  (result ↔ balanced_paren_non_computable brackets '<' '>')
-- program terminates
∃ result, impl brackets = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def balanced_paren_count (s : List Char) (open_char close_char : Char) : Int :=
  s.foldl (fun acc c => 
    if c = open_char then acc + 1 
    else if c = close_char then acc - 1 
    else acc) 0

-- LLM HELPER
def balanced_paren_never_negative (s : List Char) (open_char close_char : Char) : Bool :=
  (s.scanl (fun acc c => 
    if c = open_char then acc + 1 
    else if c = close_char then acc - 1 
    else acc) 0).all (fun x => x ≥ 0)

-- LLM HELPER
def balanced_paren_computable (s : String) (open_char close_char : Char) : Bool :=
  balanced_paren_count s.data open_char close_char = 0 ∧ 
  balanced_paren_never_negative s.data open_char close_char

-- LLM HELPER
lemma balanced_paren_equiv (s : String) (open_char close_char : Char) :
  balanced_paren_computable s open_char close_char ↔ balanced_paren_non_computable s open_char close_char :=
by
  constructor
  · intro h
    exact balanced_paren_computable_iff_non_computable.mp h
  · intro h  
    exact balanced_paren_computable_iff_non_computable.mpr h

def implementation (brackets: String) : Bool := 
  balanced_paren_computable brackets '<' '>'

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  unfold problem_spec
  use balanced_paren_computable brackets '<' '>'
  constructor
  · rfl
  · intro h
    unfold implementation
    exact balanced_paren_equiv brackets '<' '>'