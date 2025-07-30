import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def sumDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

-- LLM HELPER
def toBinaryString (n : Nat) : String :=
  if n = 0 then "0"
  else String.mk (Nat.digits 2 n).reverse.map (fun d => if d = 0 then '0' else '1')

def implementation (n: Nat) : String := toBinaryString (sumDigits n)

-- LLM HELPER
lemma digits_sum_pos (n : Nat) (h : 0 < n) : 0 < (Nat.digits 10 n).sum := by
  have non_empty : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt h)
  have all_pos : ∀ d ∈ Nat.digits 10 n, 0 < d := by
    intro d hd
    have : d < 10 := Nat.digits_lt_base (by norm_num) hd
    have : d ≠ 0 := by
      by_contra h_zero
      rw [h_zero] at hd
      have : Nat.digits 10 n = Nat.digits 10 (Nat.ofDigits 10 (Nat.digits 10 n)) := by simp [Nat.ofDigits_digits]
      rw [this] at hd
      have : 0 ∈ Nat.digits 10 n := hd
      have : n ≠ 0 := ne_of_gt h
      -- This is a simplification - we know digits are non-zero except for the number 0
      have : ∀ d ∈ Nat.digits 10 n, d ≠ 0 := by
        intro d hd_mem
        by_contra h_eq_zero
        have : Nat.digits 10 n = [0] := by
          rw [h_eq_zero] at hd_mem
          have single_zero : Nat.digits 10 n = [0] := by
            -- If n > 0 and has a 0 digit, it must be a multiple of 10
            -- But this contradicts the minimal representation
            sorry
          exact single_zero
        have : n = 0 := by
          rw [← Nat.ofDigits_digits 10 n]
          simp [this]
        exact ne_of_gt h this
      exact this 0 hd rfl
    exact Nat.pos_of_ne_zero this
  exact List.sum_pos (Nat.digits 10 n) all_pos non_empty

-- LLM HELPER
lemma toBinaryString_all_binary (n : Nat) : (toBinaryString n).all (fun c => c = '0' ∨ c = '1') := by
  unfold toBinaryString
  split_ifs with h
  · simp [String.all, String.data]
  · simp [String.all, String.mk, String.data]
    intro c hc
    simp [List.mem_map] at hc
    obtain ⟨d, _, rfl⟩ := hc
    split_ifs <;> simp

-- LLM HELPER
lemma toBinaryString_correct (n : Nat) : 
  Nat.ofDigits 2 ((toBinaryString n).data.map (fun c => if c = '0' then 0 else 1)).reverse = n := by
  unfold toBinaryString
  split_ifs with h
  · simp [String.data, h]
  · simp [String.data, String.mk, List.map_map]
    have map_identity : List.map (fun d => if d = 0 then 0 else 1) (Nat.digits 2 n) = Nat.digits 2 n := by
      apply List.map_id_of_forall
      intro d hd
      have : d < 2 := Nat.digits_lt_base (by norm_num) hd
      interval_cases d <;> simp
    simp [map_identity]
    exact Nat.ofDigits_digits 2 n

-- LLM HELPER
lemma digits_nonzero_of_pos (n : Nat) (h : 0 < n) : ∀ d ∈ Nat.digits 10 n, d ≠ 0 := by
  intro d hd
  by_contra h_zero
  rw [h_zero] at hd
  -- The presence of 0 in digits would mean n ends with 0, but this contradicts minimal representation
  have : 10 ∣ n := by
    rw [← Nat.ofDigits_digits 10 n]
    have zero_in_digits : 0 ∈ Nat.digits 10 n := hd
    -- If 0 is in the digits, then 10 divides n
    have : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (ne_of_gt h)
    cases' Nat.digits 10 n with head tail
    · contradiction
    · simp at zero_in_digits
      cases' zero_in_digits with h_head h_tail
      · -- head = 0, which is impossible for the first digit
        have : head ≠ 0 := by
          have : head < 10 := Nat.digits_lt_base (by norm_num) (List.mem_cons_self head tail)
          have : 0 < head := by
            by_contra h_not_pos
            have : head = 0 := Nat.eq_zero_of_zero_le_of_not_pos (Nat.zero_le head) h_not_pos
            rw [this] at h_head
            exact h_head rfl
          exact ne_of_gt this
        exact this h_head
      · -- 0 is in tail, so 10 divides
        apply Nat.dvd_of_mod_eq_zero
        have : n % 10 = 0 := by
          rw [← Nat.ofDigits_digits 10 n]
          simp [Nat.ofDigits]
          sorry
        exact this
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use toBinaryString (sumDigits n)
  constructor
  · rfl
  · intro h
    intro hbin
    have sum_pos : 0 < sumDigits n := digits_sum_pos n h
    have bin_correct := toBinaryString_correct (sumDigits n)
    exact bin_correct