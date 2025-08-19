import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma nat_div_pos {n k : Nat} (h_div : k ∣ n) (h_pos : k > 0) : 0 < n / k := by
  cases' h_div with m hm
  rw [hm, Nat.mul_div_cancel_left m h_pos]
  simp

-- LLM HELPER
lemma idx_bound {n k : Nat} (h_div : k ∣ n) (h_pos : k > 0) (i : Fin k) (j : Fin (n / k)) : 
    i.val * (n / k) + j.val < n := by
  cases' h_div with m hm
  rw [hm, Nat.mul_div_cancel_left m h_pos]
  have : i.val < k := i.isLt
  have : j.val < m := by
    rw [hm, Nat.mul_div_cancel_left m h_pos] at j
    exact j.isLt
  omega

-- LLM HELPER
lemma idx_unique {n k : Nat} (h_div : k ∣ n) (h_pos : k > 0) (idx : Fin n) :
    ∃! (i : Fin k) (j : Fin (n / k)), idx.val = i.val * (n / k) + j.val := by
  cases' h_div with m hm
  rw [hm, Nat.mul_div_cancel_left m h_pos]
  use ⟨idx.val / m, by
    rw [Nat.div_lt_iff_lt_mul _ h_pos]
    rw [hm]
    exact idx.isLt⟩, ⟨idx.val % m, Nat.mod_lt idx.val h_pos⟩
  constructor
  · exact Nat.div_add_mod idx.val m
  · intro i j h
    have : i.val = idx.val / m ∧ j.val = idx.val % m := by
      have h_lt : i.val < k := i.isLt
      have h_lt' : j.val < m := j.isLt
      have h_eq : idx.val = i.val * m + j.val := by rw [hm, Nat.mul_div_cancel_left m h_pos] at h; exact h
      constructor
      · rw [← Nat.div_add_mod idx.val m] at h_eq
        have h_div_eq : idx.val / m = i.val := by
          rw [Nat.add_mul_div_right _ _ h_pos] at h_eq
          simp at h_eq
          exact h_eq.symm
        exact h_div_eq
      · rw [← Nat.div_add_mod idx.val m] at h_eq
        have h_mod_eq : idx.val % m = j.val := by
          have : (idx.val / m) * m + idx.val % m = i.val * m + j.val := h_eq
          omega
        exact h_mod_eq
    exact ⟨Fin.ext this.1, Fin.ext this.2⟩

-- LLM HELPER
lemma pure_post_iff_pure_pre {α : Type*} {P : Prop} {Q : α → Prop} (f : Id α) :
    ⦃⌜P⌝⦄ f ⦃⇓result => ⌜Q result⌝⦄ ↔ (P → Q f) :=
  ⟨fun h hp => h hp, fun h hp => h hp⟩

def split {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) : 
    Id (Vector (Vector Float (n / k)) k) :=
  Vector.ofFn fun i => Vector.ofFn fun j => 
    arr.get ⟨i.val * (n / k) + j.val, idx_bound h_div h_pos i j⟩

theorem split_spec {n k : Nat} (arr : Vector Float n) (h_div : k ∣ n) (h_pos : k > 0) :
    ⦃⌜k ∣ n ∧ k > 0⌝⦄
    split arr h_div h_pos
    ⦃⇓result => ⌜(∀ i : Fin k, ∀ j : Fin (n / k), 
                  ∃ (idx : Fin n), idx.val = i.val * (n / k) + j.val ∧ 
                  (result.get i).get j = arr.get idx) ∧
                 (∀ idx : Fin n, ∃ (i : Fin k) (j : Fin (n / k)), 
                  idx.val = i.val * (n / k) + j.val ∧
                  arr.get idx = (result.get i).get j)⌝⦄ := by
  rw [pure_post_iff_pure_pre]
  intro h
  constructor
  · intro i j
    use ⟨i.val * (n / k) + j.val, idx_bound h_div h_pos i j⟩
    constructor
    · rfl
    · simp [split]
      rw [Vector.get_ofFn, Vector.get_ofFn]
  · intro idx
    obtain ⟨⟨i, j⟩, h_eq, h_unique⟩ := idx_unique h_div h_pos idx
    use i, j
    constructor
    · exact h_eq
    · simp [split]
      rw [Vector.get_ofFn, Vector.get_ofFn]
      congr 1
      rw [h_eq]