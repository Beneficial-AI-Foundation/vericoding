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
lemma aux_terminates (a b: String) (k: Nat) : 
  k < b.length → 
  (check_all_rotations.aux a b k = true ↔ 
   ∃ i : Nat, k ≤ i ∧ i < b.length ∧ a.containsSubstr (rotate_string b i)) := by
  intro hk
  induction' h : b.length - k using Nat.strong_induction_on with n ih generalizing k
  unfold check_all_rotations.aux
  by_cases hge : k >= b.length
  · omega
  · simp [hge]
    by_cases hcontains : a.containsSubstr (rotate_string b k)
    · simp [hcontains]
      constructor
      · intro
        use k
        exact ⟨le_refl k, hk, hcontains⟩
      · intro ⟨i, hle, hi, hcont⟩
        rfl
    · simp [hcontains]
      constructor
      · intro h_aux
        have hk_succ : k + 1 < b.length := by
          by_contra h_not
          push_neg at h_not
          have : k + 1 >= b.length := h_not
          have : k + 1 > k := Nat.lt_succ_self k
          have : k >= b.length := by omega
          contradiction
        have eq_refl : b.length - (k + 1) = b.length - (k + 1) := rfl
        rw [ih (b.length - (k + 1)) (by omega) (k + 1) hk_succ eq_refl] at h_aux
        obtain ⟨i, hle, hi, hcont⟩ := h_aux
        use i
        exact ⟨by omega, hi, hcont⟩
      · intro ⟨i, hle, hi, hcont⟩
        have hk_succ : k + 1 < b.length := by
          by_contra h_not
          push_neg at h_not
          have : k + 1 >= b.length := h_not
          have : i < b.length := hi
          have : k ≤ i := hle
          have : i ≤ k := by omega
          have : i = k := by omega
          rw [this] at hcont
          contradiction
        have eq_refl : b.length - (k + 1) = b.length - (k + 1) := rfl
        rw [ih (b.length - (k + 1)) (by omega) (k + 1) hk_succ eq_refl]
        by_cases h_eq : i = k
        · rw [h_eq] at hcont
          contradiction
        · use i
          exact ⟨by omega, hi, hcont⟩

-- LLM HELPER
lemma check_all_rotations_correct (a b: String) (hb: 0 < b.length) :
  check_all_rotations a b = true ↔ 
  ∃ i : Nat, i < b.length ∧ a.containsSubstr (rotate_string b i) := by
  unfold check_all_rotations
  simp [hb]
  rw [aux_terminates a b 0 (by omega)]
  constructor
  · intro ⟨i, _, hi, hcont⟩
    exact ⟨i, hi, hcont⟩
  · intro ⟨i, hi, hcont⟩
    exact ⟨i, by omega, hi, hcont⟩

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
            · rw [← check_all_rotations_correct] at h_impl
              · obtain ⟨i, hi, hcont⟩ := h_impl
                use i
                exact ⟨hi, hcont⟩
              · exact h_nonempty
      · intro ⟨h_len, h_exists⟩
        unfold implementation
        by_cases h1 : b.length = 0
        · contradiction
        · by_cases h2 : b.length > a.length
          · omega
          · simp [h1, h2]
            rw [check_all_rotations_correct]
            · obtain ⟨i, hi, hcont⟩ := h_exists
              use i
              exact ⟨hi, hcont⟩
            · exact h_nonempty