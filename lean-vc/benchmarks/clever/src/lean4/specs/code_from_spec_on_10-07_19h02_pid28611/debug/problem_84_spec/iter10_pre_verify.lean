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
      have : 10 ∣ n := by
        rw [← Nat.ofDigits_digits 10 n]
        have : 0 ∈ Nat.digits 10 n := hd
        rw [Nat.dvd_iff_mod_eq_zero]
        have : n % 10 = List.head (Nat.digits 10 n) := by
          rw [← Nat.mod_two_eq_zero_or_one.left] at h_zero
          cases' Nat.digits 10 n with head tail
          · rw [List.mem_nil_iff] at hd
            exact hd
          · simp at hd
            cases' hd with h_head h_tail
            · rw [← h_head]
              exact Nat.digits_mod_base 10 n (by norm_num)
            · have : List.head (head :: tail) = head := rfl
              rw [this]
              rw [← h_head]
              exact Nat.digits_mod_base 10 n (by norm_num)
        rw [this, h_zero]
      have : n = 0 := by
        have : n % 10 = 0 := Nat.mod_eq_zero_of_dvd this
        cases' n with n'
        · rfl
        · have : Nat.succ n' % 10 = 0 := this
          have : 0 < Nat.succ n' := Nat.succ_pos n'
          have : Nat.succ n' ≥ 10 := by
            by_contra h_not_ge
            have : Nat.succ n' < 10 := Nat.lt_of_not_ge h_not_ge
            have : Nat.succ n' % 10 = Nat.succ n' := Nat.mod_eq_of_lt this
            rw [this] at this
            have : 0 < Nat.succ n' := Nat.succ_pos n'
            linarith
          have : 10 ≤ Nat.succ n' := this
          have : Nat.succ n' = 10 * (Nat.succ n' / 10) := by
            rw [← Nat.div_add_mod (Nat.succ n') 10]
            rw [this]
            simp
          have : 0 < Nat.succ n' / 10 := by
            have : 10 ≤ Nat.succ n' := this
            exact Nat.div_pos this (by norm_num)
          have : Nat.digits 10 (Nat.succ n') = [0] := by
            have : Nat.succ n' % 10 = 0 := this
            rw [← Nat.ofDigits_digits 10 (Nat.succ n')]
            simp [Nat.ofDigits]
            exact this
          have : List.length (Nat.digits 10 (Nat.succ n')) = 1 := by
            rw [this]
            simp
          have : 1 = Nat.log 10 (Nat.succ n') + 1 := by
            rw [← Nat.length_digits 10 (Nat.succ n') (by norm_num)]
            exact this.symm
          have : Nat.log 10 (Nat.succ n') = 0 := by linarith
          have : Nat.succ n' < 10 := by
            have : Nat.succ n' < 10 ^ (Nat.log 10 (Nat.succ n') + 1) := Nat.lt_pow_succ_log_base (by norm_num) (Nat.succ_pos n')
            rw [this] at this
            simp at this
            exact this
          have : Nat.succ n' ≥ 10 := this
          linarith
      exact ne_of_gt h this
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