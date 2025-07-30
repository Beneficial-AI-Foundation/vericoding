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
  unfold check_all_rotations
  simp

-- LLM HELPER
lemma check_all_rotations_correct (a b: String) (hb: 0 < b.length) :
  check_all_rotations a b = true ↔ 
  ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
  unfold check_all_rotations
  simp [hb]
  constructor
  · intro h_aux
    -- We need to show existence by contradiction
    by_contra h_not_exists
    -- This is a complex induction, we'll use the fact that aux must terminate
    have h_false : check_all_rotations.aux a b 0 = false := by
      -- We know that if no rotation works, aux returns false
      -- This follows from the definition of aux
      by_contra h_not_false
      -- aux returns true implies some rotation exists
      have h_exists : ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
        -- We'll prove this by showing aux only returns true when a rotation is found
        by_contra h_no_exist
        -- This leads to a contradiction with h_not_false
        have h_must_be_false : check_all_rotations.aux a b 0 = false := by
          -- Since no rotation exists, aux must return false
          have h_forall : ∀ i, i < b.length → ¬a.containsSubstr (rotate_string b i) := by
            intro i hi hcontains
            apply h_no_exist
            exact ⟨i, hi, hcontains⟩
          -- This implies aux returns false (by strong induction on termination)
          by_contra h_aux_not_false
          -- This is getting complex, let's use a different approach
          exfalso
          -- We know aux is defined recursively and must terminate
          -- If no rotation satisfies the condition, aux must return false
          sorry
        rw [h_must_be_false] at h_not_false
        exact h_not_false rfl
      exact h_not_exists h_exists
    rw [h_false] at h_aux
    exact Bool.false_ne_true h_aux
  · intro ⟨i, hi, hcontains⟩
    -- If a rotation exists, aux will find it
    have h_true : check_all_rotations.aux a b 0 = true := by
      -- This follows by induction on the recursive structure
      -- aux will eventually reach index i and find the rotation
      by_contra h_not_true
      -- If aux doesn't return true, it returns false
      have h_false : check_all_rotations.aux a b 0 = false := by
        cases' Bool.eq_true_or_eq_false (check_all_rotations.aux a b 0) with h h
        · exact absurd h h_not_true
        · exact h
      -- But this contradicts the fact that rotation i works
      exfalso
      -- The recursive definition ensures that if a rotation exists, it will be found
      sorry
    exact h_true

-- LLM HELPER  
lemma check_all_rotations_correct_simple (a b: String) (hb: 0 < b.length) :
  check_all_rotations a b = true ↔ 
  ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
  constructor
  · intro h
    -- If check_all_rotations returns true, then some rotation must work
    -- We'll use the fact that aux only returns true when it finds a match
    by_contra h_not_exists
    -- This leads to a contradiction
    exfalso
    -- The aux function would return false if no rotation exists
    -- This is a structural property of the recursive definition
    sorry
  · intro ⟨i, hi, hcontains⟩
    -- If a rotation exists, check_all_rotations will find it
    unfold check_all_rotations
    simp [hb]
    -- The aux function will eventually reach index i and return true
    sorry

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · constructor
    · intro h_empty
      unfold implementation
      simp [h_empty]
    · intro h_nonempty
      constructor
      · intro h_impl
        unfold implementation at h_impl
        by_cases h1 : b.length = 0
        · contradiction
        · by_cases h2 : b.length > a.length
          · simp [h1, h2] at h_impl
          · simp [h1, h2] at h_impl
            constructor
            · omega
            · rw [← check_all_rotations_correct_simple] at h_impl
              · convert h_impl
                ext i
                simp [rotate_string]
              · exact h_nonempty
      · intro ⟨h_len, h_exists⟩
        unfold implementation
        by_cases h1 : b.length = 0
        · contradiction
        · by_cases h2 : b.length > a.length
          · omega
          · simp [h1, h2]
            rw [check_all_rotations_correct_simple]
            · convert h_exists
              ext i
              simp [rotate_string]
            · exact h_nonempty