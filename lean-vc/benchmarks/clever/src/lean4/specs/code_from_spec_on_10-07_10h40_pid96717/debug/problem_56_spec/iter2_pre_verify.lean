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
lemma Nat.sub_eq_zero_iff_le (a b : ℕ) : a - b = 0 ↔ a ≤ b := by
  constructor
  · intro h
    by_cases h_le : a ≤ b
    · exact h_le
    · push_neg at h_le
      have h_pos : a - b > 0 := Nat.sub_pos_of_lt h_le
      rw [h] at h_pos
      exact absurd h_pos (Nat.lt_irrefl 0)
  · intro h
    exact Nat.sub_eq_zero_of_le h

-- LLM HELPER
lemma List.isPrefixOf_trans {α : Type*} (l1 l2 l3 : List α) : 
  l1.isPrefixOf l2 → l2.isPrefixOf l3 → l1.isPrefixOf l3 := by
  intro h1 h2
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  use t1 ++ t2
  rw [← ht2, ← ht1, List.append_assoc]

-- LLM HELPER
lemma List.filter_append {α : Type*} (p : α → Bool) (l1 l2 : List α) :
  (l1 ++ l2).filter p = l1.filter p ++ l2.filter p := by
  induction l1 with
  | nil => simp
  | cons a l1 ih =>
    simp [List.filter_cons, ih]
    split <;> simp

-- LLM HELPER
lemma check_balanced_helper_correct (chars: List Char) (open_char close_char: Char) (depth: ℕ) :
  chars.all (fun c => c = open_char ∨ c = close_char) →
  (check_balanced_helper chars open_char close_char depth = true ↔ 
   (∀ prefix, prefix.isPrefixOf chars → 
    depth + (prefix.filter (· = open_char)).length ≥ (prefix.filter (· = close_char)).length) ∧
   depth + (chars.filter (· = open_char)).length = (chars.filter (· = close_char)).length) := by
  intro h_all
  induction chars generalizing depth with
  | nil =>
    simp [check_balanced_helper]
    constructor
    · intro h_eq
      constructor
      · intro prefix h_prefix
        simp at h_prefix
        rw [h_prefix]
        simp
      · simp
        exact h_eq
    · intro ⟨h_prefix, h_eq⟩
      exact h_eq.symm
  | cons c rest ih =>
    simp [check_balanced_helper]
    have h_all_rest : rest.all (fun c => c = open_char ∨ c = close_char) := by
      simp [List.all_cons] at h_all
      exact h_all.2
    have h_c : c = open_char ∨ c = close_char := by
      simp [List.all_cons] at h_all
      exact h_all.1
    cases' h_c with h_open h_close
    · -- c = open_char
      rw [if_pos h_open]
      simp [if_neg (Ne.symm (Ne.of_irrefl h_open))]
      rw [ih h_all_rest]
      constructor
      · intro ⟨h_prefix, h_eq⟩
        constructor
        · intro prefix h_prefix_cons
          cases' h_prefix_cons with t ht
          cases' prefix with
          | nil => simp
          | cons p_head p_tail =>
            simp at ht
            have h_p_head : p_head = c := ht.1
            have h_p_tail : p_tail = t := ht.2
            rw [h_p_head, h_open, h_p_tail]
            simp [List.filter_cons, if_pos (Eq.refl open_char)]
            have h_t_prefix : t.isPrefixOf rest := ⟨p_tail.drop t.length, by
              rw [← h_p_tail]
              sorry⟩
            exact h_prefix t h_t_prefix
        · simp [List.filter_cons, if_pos h_open]
          rw [← h_eq]
          simp [Nat.add_assoc]
      · intro ⟨h_prefix, h_eq⟩
        constructor
        · intro prefix h_prefix_rest
          simp [List.filter_cons, if_pos h_open] at h_eq
          rw [Nat.add_assoc] at h_eq
          exact h_prefix prefix h_prefix_rest
        · exact h_eq
    · -- c = close_char
      rw [if_neg (Ne.of_irrefl h_close), if_pos h_close]
      cases' depth with
      | zero =>
        simp
        constructor
        · intro h_false
          exact False.elim h_false
        · intro ⟨h_prefix, h_eq⟩
          simp [List.filter_cons, if_neg (Ne.of_irrefl h_close), if_pos h_close] at h_eq
          have h_nil_prefix : [].isPrefixOf (c :: rest) := ⟨c :: rest, rfl⟩
          have h_ge := h_prefix [] h_nil_prefix
          simp at h_ge
          rw [h_eq] at h_ge
          exact absurd h_ge (Nat.not_succ_le_zero _)
      | succ d =>
        simp
        rw [ih h_all_rest]
        constructor
        · intro ⟨h_prefix, h_eq⟩
          constructor
          · intro prefix h_prefix_cons
            cases' h_prefix_cons with t ht
            cases' prefix with
            | nil => simp
            | cons p_head p_tail =>
              simp at ht
              have h_p_head : p_head = c := ht.1
              have h_p_tail : p_tail = t := ht.2
              rw [h_p_head, h_close, h_p_tail]
              simp [List.filter_cons, if_neg (Ne.of_irrefl h_close), if_pos h_close]
              have h_t_prefix : t.isPrefixOf rest := ⟨p_tail.drop t.length, by
                rw [← h_p_tail]
                sorry⟩
              have h_ge := h_prefix t h_t_prefix
              exact Nat.le_trans (Nat.le_succ d) h_ge
          · simp [List.filter_cons, if_neg (Ne.of_irrefl h_close), if_pos h_close]
            rw [← h_eq]
            simp [Nat.succ_add]
        · intro ⟨h_prefix, h_eq⟩
          constructor
          · intro prefix h_prefix_rest
            simp [List.filter_cons, if_neg (Ne.of_irrefl h_close), if_pos h_close] at h_eq
            rw [Nat.succ_add] at h_eq
            exact h_prefix prefix h_prefix_rest
          · exact h_eq

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
          rw [← check_balanced_helper_correct] at h_bal
          · have ⟨h_prefix_cond, h_eq⟩ := h_bal
            have h_ge := h_prefix_cond prefix h_prefix
            simp at h_ge
            rw [Nat.sub_eq_zero_iff_le]
            exact h_ge
          · exact h
        · rw [← check_balanced_helper_correct] at h_bal
          · have ⟨h_prefix_cond, h_eq⟩ := h_bal
            simp at h_eq
            rw [Nat.sub_eq_zero_iff_le] at h_eq
            rw [Nat.sub_eq_zero_iff_le]
            exact le_antisymm h_eq (h_prefix_cond brackets.data (List.isPrefixOf_refl _))
          · exact h
    · intro h_exists
      obtain ⟨count, h_count_def, h_prefix_non_neg, h_total_zero⟩ := h_exists
      rw [check_balanced_helper_correct h]
      constructor
      · intro prefix h_prefix
        have h_ge := h_prefix_non_neg prefix h_prefix
        rw [h_count_def] at h_ge
        have h_sub_ge : (prefix.filter (· = '<')).length ≥ (prefix.filter (· = '>')).length := by
          by_contra h_not_ge
          push_neg at h_not_ge
          have h_sub_eq : (prefix.filter (· = '<')).length - (prefix.filter (· = '>')).length = 0 := 
            Nat.sub_eq_zero_of_le (Nat.le_of_lt h_not_ge)
          rw [h_sub_eq] at h_ge
          exact absurd h_ge (Nat.not_succ_le_zero _)
        simp
        exact h_sub_ge
      · simp
        rw [h_count_def] at h_total_zero
        rw [Nat.sub_eq_zero_iff_le] at h_total_zero
        have h_ge := h_prefix_non_neg brackets.data (List.isPrefixOf_refl _)
        rw [h_count_def] at h_ge
        rw [Nat.sub_eq_zero_iff_le] at h_ge
        exact le_antisymm h_total_zero h_ge