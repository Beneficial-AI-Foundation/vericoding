/- 
function_signature: "def correct_bracketing(brackets: str) -> Bool"
docstring: |
    brackets is a string of "(" and ")".
    return True if every opening bracket has a corresponding closing bracket.
test_cases:
  - input: "("
    expected_output: False
  - input: "()"
    expected_output: True
  - input: "(()())"
    expected_output: True
  - input: ")(()"
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
def balance_check_aux (chars : List Char) (balance : Int) : Bool :=
  match chars with
  | [] => balance = 0
  | c :: rest =>
    if c = '(' then
      balance_check_aux rest (balance + 1)
    else if c = ')' then
      if balance > 0 then
        balance_check_aux rest (balance - 1)
      else
        false
    else
      balance_check_aux rest balance

def implementation (paren_string: String) : Bool :=
  balance_check_aux paren_string.data 0

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(brackets: String) :=
-- spec
let spec (result: Bool) :=
  brackets.data.all (fun c => c = '(' ∨ c = ')') →
  (result ↔ balanced_paren_non_computable brackets '(' ')')
-- program terminates
∃ result, impl brackets = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma balance_check_aux_correct (chars : List Char) (init_balance : Int) :
  chars.all (fun c => c = '(' ∨ c = ')') →
  init_balance ≥ 0 →
  (balance_check_aux chars init_balance = true ↔ 
   (∀ i ≤ chars.length, 
    init_balance + (chars.take i).count '(' - (chars.take i).count ')' ≥ 0) ∧
   init_balance + chars.count '(' - chars.count ')' = 0) := by
  intro h_all h_nonneg
  induction chars using List.rec generalizing init_balance with
  | nil =>
    simp [balance_check_aux]
    intro h
    constructor
    · intro i hi
      simp at hi
      cases hi with
      | refl => simp
    · exact h
  | cons c rest ih =>
    simp [balance_check_aux]
    have h_all_split : List.all (c :: rest) (fun c => c = '(' ∨ c = ')') = true → 
      c = '(' ∨ c = ')' ∧ List.all rest (fun c => c = '(' ∨ c = ')') = true := by
      intro h
      simp [List.all_cons] at h
      exact h
    have ⟨h_c, h_all_rest⟩ := h_all_split h_all
    cases h_c with
    | inl h_open =>
      simp [h_open]
      have h_pos : init_balance + 1 ≥ 0 := by omega
      rw [ih init_balance h_all_rest h_pos]
      simp [h_open]
      constructor
      · intro ⟨h1, h2⟩
        constructor
        · intro i hi
          cases i with
          | zero => simp; exact h_nonneg
          | succ j =>
            simp
            have : j ≤ rest.length := by omega
            exact h1 j this
        · omega
      · intro ⟨h1, h2⟩
        constructor
        · intro j hj
          have : j + 1 ≤ (c :: rest).length := by simp; omega
          have := h1 (j + 1) this
          simp [h_open] at this
          exact this
        · omega
    | inr h_close =>
      simp [h_close]
      by_cases h_pos : init_balance > 0
      · simp [h_pos]
        have h_nonneg' : init_balance - 1 ≥ 0 := by omega
        rw [ih (init_balance - 1) h_all_rest h_nonneg']
        simp [h_close]
        constructor
        · intro ⟨h1, h2⟩
          constructor
          · intro i hi
            cases i with
            | zero => simp; exact h_nonneg
            | succ j =>
              simp
              have : j ≤ rest.length := by omega
              have := h1 j this
              omega
          · omega
        · intro ⟨h1, h2⟩
          constructor
          · intro j hj
            have : j + 1 ≤ (c :: rest).length := by simp; omega
            have := h1 (j + 1) this
            simp [h_close] at this
            omega
          · omega
      · simp [h_pos]
        intro h_contra
        exfalso
        have h0 : init_balance = 0 := by omega
        rw [h0] at h_contra
        have := h_contra 1 (by simp)
        simp [h_close] at this
        omega

-- LLM HELPER  
lemma all_bool_to_prop (l : List Char) :
  l.all (fun c => decide (c = '(' ∨ c = ')')) = true ↔ ∀ x ∈ l, x = '(' ∨ x = ')' := by
  simp [List.all_eq_true]

-- LLM HELPER
lemma implementation_correct_aux (paren_string : String) :
  (paren_string.data.all fun c => decide (c = '(' ∨ c = ')')) = true →
  (balance_check_aux paren_string.data 0 = true ↔ balanced_paren_non_computable paren_string '(' ')') := by
  intro h_all
  have h_all_prop : ∀ x ∈ paren_string.data, x = '(' ∨ x = ')' := by
    rw [← all_bool_to_prop]
    exact h_all
  simp [balanced_paren_non_computable]
  have h_all_simple : paren_string.data.all (fun c => c = '(' ∨ c = ')') = true := by
    simp [List.all_eq_true]
    exact h_all_prop
  rw [balance_check_aux_correct paren_string.data 0 h_all_simple (by norm_num)]
  simp
  intro h_balanced
  simp [Int.coe_nat_sub_of_le]
  omega

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  simp [problem_spec]
  use implementation brackets
  constructor
  · rfl
  · intro h_all
    exact implementation_correct_aux brackets h_all

-- #test implementation "(" = false
-- #test implementation "()" = true
-- #test implementation "(()())" = true
-- #test implementation ")(()" = false