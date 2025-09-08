/- 
function_signature: "def correct_bracketing(brackets: str) -> Bool"
docstring: |
    brackets is a string of "<" and ">".
    return True if every opening bracket has a corresponding closing bracket, i.e., (each open bracket is properly closed)
test_cases:
  - input: "<"
    expected_output: False
  - input: "<>"
    expected_output: True
  - input: "<<><>>"
    expected_output: True
  - input: "><<>"
    expected_output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: balanced_paren_non_computable
use: |
  Non-computable definition to check if a string is balanced with respect to parentheses.
problems:
  - 1
  - 6
  - 132
sample_problems:
  - 0
-/
def balanced_paren_non_computable
(paren_string: String) (bracket_type_left : Char) (bracket_type_right: Char): Prop
:=
let chars := paren_string.toList;
(∀ (i : ℕ), i ≤ chars.length → ((chars.take i).count bracket_type_right) ≤ ((chars.take i).count bracket_type_left)) ∧
(chars.count bracket_type_left = chars.count bracket_type_right)

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def check_balance_aux (chars : List Char) : Int → Bool
  | balance => 
    match chars with
    | [] => balance = 0
    | '<' :: rest => if balance < 0 then false else check_balance_aux rest (balance + 1)
    | '>' :: rest => check_balance_aux rest (balance - 1)
    | _ :: rest => check_balance_aux rest balance

def implementation (brackets: String) : Bool :=
  check_balance_aux brackets.toList 0

-- LLM HELPER
lemma count_take_mono (l : List Char) (c : Char) (i j : ℕ) (h : i ≤ j) : 
  (l.take i).count c ≤ (l.take j).count c := by
  have : l.take i <:+ l.take j := List.take_prefix_take h
  exact List.count_le_of_sublist this

-- LLM HELPER
lemma check_balance_aux_correct (chars : List Char) (init_balance : Int) :
  chars.all (fun c => c = '<' ∨ c = '>') →
  check_balance_aux chars init_balance = true ↔ 
  (∀ (i : ℕ), i ≤ chars.length → 
    init_balance + (chars.take i).count '<' - (chars.take i).count '>' ≥ 0) ∧
  (init_balance + chars.count '<' - chars.count '>' = 0) := by
  intro h_valid
  induction chars generalizing init_balance with
  | nil => 
    simp [check_balance_aux]
    constructor
    · intro h
      constructor
      · intro i hi
        simp at hi
        rw [hi]
        simp
      · exact h
    · intro ⟨_, h⟩
      exact h
  | cons head tail ih =>
    cases head with
    | mk val =>
      have h_head : head = '<' ∨ head = '>' := by
        simp [List.all_cons] at h_valid
        exact h_valid.1
      have h_tail : tail.all (fun c => c = '<' ∨ c = '>') := by
        simp [List.all_cons] at h_valid
        exact h_valid.2
      cases h_head with
      | inl h_lt =>
        simp [check_balance_aux, h_lt]
        split_ifs with h_neg
        · simp
          constructor
          · intro h_false
            cases h_false
          · intro ⟨h_all, _⟩
            have : init_balance ≥ 0 := by
              have := h_all 0 (by simp)
              simp at this
              exact this
            omega
        · rw [ih h_tail]
          simp [h_lt]
          constructor
          · intro ⟨h_all, h_eq⟩
            constructor
            · intro i hi
              cases i with
              | zero => simp; omega
              | succ j =>
                simp [List.take_succ_cons]
                have := h_all j (by omega)
                simp [h_lt] at this
                omega
            · simp [h_lt] at h_eq
              omega
          · intro ⟨h_all, h_eq⟩
            constructor
            · intro i hi
              have := h_all (i + 1) (by omega)
              simp [List.take_succ_cons, h_lt] at this
              omega
            · simp [h_lt]
              omega
      | inr h_gt =>
        simp [check_balance_aux, h_gt]
        rw [ih h_tail]
        simp [h_gt]
        constructor
        · intro ⟨h_all, h_eq⟩
          constructor
          · intro i hi
            cases i with
            | zero => simp; exact le_refl _
            | succ j =>
              simp [List.take_succ_cons]
              have := h_all j (by omega)
              simp [h_gt] at this
              omega
          · simp [h_gt] at h_eq
            omega
        · intro ⟨h_all, h_eq⟩
          constructor
          · intro i hi
            have := h_all (i + 1) (by omega)
            simp [List.take_succ_cons, h_gt] at this
            omega
          · simp [h_gt]
            omega

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

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  unfold problem_spec
  use implementation brackets
  constructor
  · rfl
  · intro h_valid
    unfold implementation balanced_paren_non_computable
    simp [String.toList]
    rw [check_balance_aux_correct]
    · simp
      constructor
      · intro ⟨h_all, h_eq⟩
        constructor
        · intro i hi
          have := h_all i hi
          omega
        · omega
      · intro ⟨h_all, h_eq⟩
        constructor
        · intro i hi
          have := h_all i hi
          omega
        · omega
    · exact h_valid

-- #test implementation "<" = false
-- #test implementation "<>" = true
-- #test implementation "<<><>>" = true
-- #test implementation "><<>" = false