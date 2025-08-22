import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def rotate_string (s: String) (i: Nat) : String :=
  s.drop i ++ s.take i

-- LLM HELPER
def check_all_rotations (a b: String) : Bool :=
  if b.length = 0 then true
  else
    let rec aux (k: Nat) : Bool :=
      if k >= b.length then false
      else
        let rotation := rotate_string b k
        if a.containsSubstr rotation then true
        else aux (k + 1)
    termination_by b.length - k
    aux 0

def implementation (a b: String) : Bool := 
  if b.length = 0 then true
  else if b.length > a.length then false
  else check_all_rotations a b

-- LLM HELPER
lemma rotate_string_def (s: String) (i: Nat) : 
  rotate_string s i = s.drop i ++ s.take i := by
  rfl

-- LLM HELPER
lemma check_all_rotations_empty (a: String) : 
  check_all_rotations a "" = true := by
  simp [check_all_rotations]

-- LLM HELPER
lemma check_all_rotations_correct (a b: String) (hb: 0 < b.length) :
  check_all_rotations a b = true ↔ 
  ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
  simp [check_all_rotations, hb]
  constructor
  · intro h_aux
    -- If aux returns true, then some rotation was found
    have h_exists : ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
      -- This follows from the structure of aux
      by_contra h_not_exists
      -- aux would return false if no rotation exists
      have h_false : check_all_rotations.aux a b 0 = false := by
        -- This would require induction on the recursive structure
        induction' Nat.lt_wf_rel.1 (b.length - 0) using Nat.strong_induction_on with n ih
        simp [check_all_rotations.aux]
        split_ifs with h1 h2
        · rfl
        · exfalso
          apply h_not_exists
          exact ⟨0, Nat.not_le.mp h1, h2⟩
        · apply ih
          · simp
            exact Nat.sub_lt (Nat.not_le.mp h1) (Nat.zero_lt_one)
          · intro i hi hcontains
            apply h_not_exists
            exact ⟨i + 1, Nat.lt_of_succ_le (Nat.le_of_not_gt h1), hcontains⟩
      rw [h_false] at h_aux
      exact Bool.false_ne_true h_aux
    exact h_exists
  · intro ⟨i, hi, hcontains⟩
    -- If a rotation exists, aux will find it
    have h_true : check_all_rotations.aux a b 0 = true := by
      -- This follows by strong induction
      induction' i using Nat.strong_induction_on with j ih
      simp [check_all_rotations.aux]
      split_ifs with h1 h2
      · omega
      · exact h2
      · apply ih
        · exact hi
        · exact hcontains
    exact h_true

-- LLM HELPER
lemma implementation_empty_case (a: String) :
  implementation a "" = true := by
  simp [implementation]

-- LLM HELPER
lemma implementation_length_case (a b: String) (h: b.length > a.length) :
  implementation a b = false := by
  simp [implementation]
  split_ifs with h1 h2
  · contradiction
  · rfl

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · constructor
    · intro h_empty
      simp [implementation]
      rw [h_empty]
      simp
    · intro h_nonempty
      constructor
      · intro h_impl
        simp [implementation] at h_impl
        by_cases h1 : b.length = 0
        · contradiction
        · by_cases h2 : b.length > a.length
          · simp [h1, h2] at h_impl
          · simp [h1, h2] at h_impl
            constructor
            · omega
            · rw [check_all_rotations_correct] at h_impl
              · exact h_impl
              · exact h_nonempty
      · intro ⟨h_len, h_exists⟩
        simp [implementation]
        by_cases h1 : b.length = 0
        · contradiction
        · by_cases h2 : b.length > a.length
          · omega
          · simp [h1, h2]
            rw [check_all_rotations_correct]
            · exact h_exists
            · exact h_nonempty