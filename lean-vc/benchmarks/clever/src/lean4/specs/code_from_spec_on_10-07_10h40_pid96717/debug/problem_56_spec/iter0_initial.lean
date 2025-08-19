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
def balanced_paren_non_computable (s: String) (open_char close_char: Char) : Prop :=
  ∃ (count: List Char → ℕ), 
    (∀ chars, count chars = (chars.filter (· = open_char)).length - (chars.filter (· = close_char)).length) ∧
    (∀ prefix, prefix.isPrefixOf s.data → count prefix ≥ 0) ∧
    count s.data = 0

-- LLM HELPER
def check_balanced_helper (chars: List Char) (open_char close_char: Char) (depth: ℕ) : Bool :=
  match chars with
  | [] => depth = 0
  | c :: rest =>
    if c = open_char then
      check_balanced_helper rest open_char close_char (depth + 1)
    else if c = close_char then
      if depth = 0 then false
      else check_balanced_helper rest open_char close_char (depth - 1)
    else
      check_balanced_helper rest open_char close_char depth

def implementation (brackets: String) : Bool := 
  check_balanced_helper brackets.data '<' '>' 0

-- LLM HELPER
lemma check_balanced_helper_correct (chars: List Char) (open_char close_char: Char) (depth: ℕ) :
  chars.all (fun c => c = open_char ∨ c = close_char) →
  (check_balanced_helper chars open_char close_char depth = true ↔ 
   (∀ prefix, prefix.isPrefixOf chars → 
    depth + (prefix.filter (· = open_char)).length ≥ (prefix.filter (· = close_char)).length) ∧
   depth + (chars.filter (· = open_char)).length = (chars.filter (· = close_char)).length) := by
  sorry

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  unfold problem_spec
  unfold implementation
  use check_balanced_helper brackets.data '<' '>' 0
  constructor
  · rfl
  · intro h
    unfold balanced_paren_non_computable
    constructor
    · intro h_bal
      use fun chars => (chars.filter (· = '<')).length - (chars.filter (· = '>')).length
      constructor
      · intro chars
        rfl
      · constructor
        · intro prefix h_prefix
          sorry
        · sorry
    · intro h_exists
      obtain ⟨count, h_count_def, h_prefix_non_neg, h_total_zero⟩ := h_exists
      sorry