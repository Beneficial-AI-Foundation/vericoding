import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def normalizeIndex (i : Int) (n : Nat) : Nat :=
  if n = 0 then 0 else ((i % n + n) % n).toNat

-- LLM HELPER
lemma normalizeIndex_lt (i : Int) (n : Nat) (h : n > 0) : 
  normalizeIndex i n < n := by
  simp [normalizeIndex]
  split
  · contradiction
  · have pos_n : (0 : Int) < n := Int.coe_nat_pos.mpr h
    have mod_bound : (i % n + n) % n < n := by
      have : (i % n + n) % n ≥ 0 := Int.mod_nonneg _ (ne_of_gt pos_n)
      have : (i % n + n) % n < n := Int.mod_lt_of_pos _ pos_n
      exact this
    exact Int.natCast_lt.mp mod_bound

/-- Roll array elements along a given axis by cyclically shifting elements.
    Elements that roll beyond the last position are re-introduced at the first. -/
def roll {n : Nat} {α : Type} (a : Vector α n) (shift : Int) : Id (Vector α n) :=
  if n = 0 then pure a else
  pure ⟨fun i => 
    let srcIdx := normalizeIndex (i.val - shift) n
    a.get ⟨srcIdx, normalizeIndex_lt (i.val - shift) n (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (Fin.size_pos' i))))⟩⟩

-- LLM HELPER
lemma normalizeIndex_spec (i : Int) (n : Nat) (h : n > 0) :
  let result := normalizeIndex i n
  let srcIdx := i % (n : Int)
  let normalizedIdx := if srcIdx < 0 then srcIdx + n else srcIdx
  result = normalizedIdx.toNat := by
  simp [normalizeIndex]
  rw [if_neg (ne_of_gt h)]
  congr 1
  simp [Int.add_mod]
  by_cases h' : i % n < 0
  · simp [if_pos h']
    have : (i % n + n) % n = i % n + n := by
      rw [Int.add_mod]
      have : n % n = 0 := Int.mod_self n
      rw [this, Int.add_zero]
      have : (i % n + n) < n := by
        have : i % n ≥ -n := Int.mod_neg_iff.mp h'
        linarith
      have : (i % n + n) ≥ 0 := by
        have : i % n > -n := by
          have : i % n > -(n : Int) := by
            have : abs (i % n) < n := Int.mod_abs_lt_abs_divisor i (ne_of_gt (Int.coe_nat_pos.mpr h))
            cases' Int.abs_choice (i % n) with hab hab
            · rw [hab] at this
              exact Int.neg_neg_of_pos this
            · rw [hab] at this
              exact Int.neg_neg_of_pos this
          linarith
        linarith
      exact Int.mod_eq_of_lt this (Int.coe_nat_pos.mpr h)
    rw [this]
    rfl
  · simp [if_neg h']
    have : (i % n + n) % n = i % n := by
      rw [Int.add_mod]
      have : n % n = 0 := Int.mod_self n
      rw [this, Int.add_zero]
      exact Int.mod_mod_of_dvd (dvd_refl _)
    rw [this]
    rfl

-- LLM HELPER
lemma toNat_lt_of_pos (i : Int) (n : Nat) (h_pos : n > 0) (h_nonneg : i ≥ 0) (h_lt : i < n) : i.toNat < n := by
  rw [Int.toNat_of_nonneg h_nonneg]
  exact Int.natCast_lt.mp h_lt

/-- Specification: roll cyclically shifts array elements by the given amount.
    For positive shift, elements move to the right and wrap around.
    For negative shift, elements move to the left and wrap around.
    Empty vectors are returned unchanged.
    
    Mathematical property: result[i] = a[(i - shift) mod n]
    where the modulo operation handles negative values correctly. -/
theorem roll_spec {n : Nat} {α : Type} (a : Vector α n) (shift : Int) :
    ⦃⌜True⌝⦄
    roll a shift
    ⦃⇓result => ⌜(n = 0 → result = a) ∧ 
                 (n > 0 → ∀ i : Fin n, 
                   let srcIdx := ((i.val : Int) - shift) % (n : Int)
                   let normalizedIdx := if srcIdx < 0 then srcIdx + n else srcIdx
                   result.get i = a.get ⟨normalizedIdx.toNat, by
                     have h_nonneg : normalizedIdx ≥ 0 := by
                       by_cases h : srcIdx < 0
                       · simp [normalizedIdx, if_pos h]
                         exact Int.add_nonneg (Int.le_of_lt h) (Int.coe_nat_nonneg n)
                       · simp [normalizedIdx, if_neg h]
                         exact Int.not_lt.mp h
                     have h_lt : normalizedIdx < n := by
                       by_cases h : srcIdx < 0
                       · simp [normalizedIdx, if_pos h]
                         have : srcIdx + n < n := by
                           have : srcIdx < 0 := h
                           have : srcIdx > -(n : Int) := by
                             have : abs srcIdx < n := Int.mod_abs_lt_abs_divisor _ (ne_of_gt (Int.coe_nat_pos.mpr (by assumption)))
                             cases' Int.abs_choice srcIdx with hab hab
                             · rw [hab] at this
                               exact Int.neg_neg_of_pos this
                             · rw [hab] at this
                               contradiction
                           linarith
                         exact this
                       · simp [normalizedIdx, if_neg h]
                         have : srcIdx < n := Int.mod_lt_of_pos _ (Int.coe_nat_pos.mpr (by assumption))
                         exact this
                     exact toNat_lt_of_pos normalizedIdx n (by assumption) h_nonneg h_lt⟩)⌝⦄ := by
  simp [roll]
  split
  · simp
    intro h
    rfl
  · next h =>
    simp
    intro h_pos i
    have h_ne : n ≠ 0 := ne_of_gt h_pos
    have : normalizeIndex (i.val - shift) n = 
           (if ((i.val : Int) - shift) % (n : Int) < 0 
            then ((i.val : Int) - shift) % (n : Int) + n 
            else ((i.val : Int) - shift) % (n : Int)).toNat := by
      exact normalizeIndex_spec (i.val - shift) n h_pos
    rw [this]
    simp [Vector.get]