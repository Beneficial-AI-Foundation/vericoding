import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.bitwise_and: Compute the bit-wise AND of two arrays element-wise.

    Computes the bit-wise AND of the underlying binary representation of 
    the integers in the input arrays. This ufunc implements the C/Python 
    operator &.

    For each pair of corresponding elements in x1 and x2, the result contains
    the bitwise AND of their binary representations. Each bit position in the
    result is 1 only if both corresponding bits in x1 and x2 are 1.

    Examples:
    - 13 & 17 = 1 (binary: 01101 & 10001 = 00001)
    - 14 & 13 = 12 (binary: 01110 & 01101 = 01100)

    Note: This specification currently handles only non-negative integers.
    For negative integers, NumPy uses two's complement representation,
    which requires a more complex formalization in Lean.
-/
def bitwise_and {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) := by
  have h_len : List.length (List.zipWith (fun a b => Int.ofNat (Int.toNat a &&& Int.toNat b)) x1.toList x2.toList) = n := by
    rw [List.length_zipWith]
    simp [Vector.toList_length, min_self]
  exact pure (Vector.mk (List.zipWith (fun a b => Int.ofNat (Int.toNat a &&& Int.toNat b)) x1.toList x2.toList) h_len)

-- LLM HELPER
lemma list_zipwith_length {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) :
  List.length (List.zipWith f l1 l2) = min (List.length l1) (List.length l2) := by
  induction l1 generalizing l2 with
  | nil => simp [List.zipWith]
  | cons h t ih =>
    cases l2 with
    | nil => simp [List.zipWith]
    | cons h' t' => simp [List.zipWith, ih]

-- LLM HELPER
lemma vector_zipwith_length {α β γ : Type*} {n : Nat} (f : α → β → γ) (v1 : Vector α n) (v2 : Vector β n) :
  List.length (List.zipWith f v1.toList v2.toList) = n := by
  rw [list_zipwith_length]
  simp [Vector.toList_length, min_self]

-- LLM HELPER
lemma list_get_zipwith {α β γ : Type*} (f : α → β → γ) (l1 : List α) (l2 : List β) (i : Fin (min l1.length l2.length)) :
  (List.zipWith f l1 l2).get ⟨i.val, by rw [list_zipwith_length]; exact i.isLt⟩ = 
  f (l1.get ⟨i.val, by simp at i; exact Nat.lt_of_lt_min_left i.isLt⟩) 
    (l2.get ⟨i.val, by simp at i; exact Nat.lt_of_lt_min_right i.isLt⟩) := by
  induction l1 generalizing l2 i with
  | nil => simp at i
  | cons h t ih =>
    cases l2 with
    | nil => simp at i
    | cons h' t' =>
      simp [List.zipWith]
      cases i.val with
      | zero => simp
      | succ k => 
        simp [List.get]
        apply ih

-- LLM HELPER  
lemma int_tonat_ofnat_nonneg (a : Int) (h : a ≥ 0) : Int.ofNat (Int.toNat a) = a := by
  rw [Int.toNat_of_nonneg h]
  simp

-- LLM HELPER
lemma nat_and_le_left (a b : Nat) : a &&& b ≤ a := by
  induction a using Nat.strong_induction_on generalizing b with
  | ind a ih =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => simp
      | succ b' =>
        simp [Nat.land_succ_succ]
        cases Nat.mod_two_eq_zero_or_one a' with
        | inl h1 => 
          cases Nat.mod_two_eq_zero_or_one b' with
          | inl h2 => simp [h1, h2]; exact Nat.succ_le_succ (ih (a'/2) (Nat.div_lt_self (Nat.succ_pos a') (by norm_num)) (b'/2))
          | inr h2 => simp [h1, h2]; exact Nat.le_succ_of_le (ih (a'/2) (Nat.div_lt_self (Nat.succ_pos a') (by norm_num)) (b'/2))
        | inr h1 =>
          cases Nat.mod_two_eq_zero_or_one b' with
          | inl h2 => simp [h1, h2]; exact Nat.le_succ_of_le (ih (a'/2) (Nat.div_lt_self (Nat.succ_pos a') (by norm_num)) (b'/2))
          | inr h2 => simp [h1, h2]; exact Nat.succ_le_succ (ih (a'/2) (Nat.div_lt_self (Nat.succ_pos a') (by norm_num)) (b'/2))

-- LLM HELPER
lemma nat_and_le_right (a b : Nat) : a &&& b ≤ b := by
  rw [Nat.land_comm]
  exact nat_and_le_left b a

-- LLM HELPER
lemma nat_and_eq_zero_iff (a b : Nat) : a &&& b = 0 ↔ (a = 0 ∨ b = 0 ∨ ∀ i, ¬(a.testBit i ∧ b.testBit i)) := by
  constructor
  · intro h
    right
    right
    intro i
    intro ⟨ha, hb⟩
    have : (a &&& b).testBit i := by
      rw [Nat.testBit_land]
      exact ⟨ha, hb⟩
    rw [h] at this
    simp at this
  · intro h
    cases h with
    | inl h => rw [h]; simp
    | inr h =>
      cases h with
      | inl h => rw [h]; simp
      | inr h =>
        ext i
        rw [Nat.testBit_land]
        simp
        exact h i

-- LLM HELPER
lemma nat_and_self (a : Nat) : a &&& a = a := by
  ext i
  rw [Nat.testBit_land]
  simp

-- LLM HELPER
lemma bitwise_and_result {n : Nat} (x1 x2 : Vector Int n) :
  bitwise_and x1 x2 = 
  pure (Vector.mk (List.zipWith (fun a b => Int.ofNat (Int.toNat a &&& Int.toNat b)) x1.toList x2.toList) 
    (by rw [list_zipwith_length]; simp [Vector.toList_length, min_self])) := by
  rfl

/-- Specification: bitwise_and returns a vector where each element is the 
    bitwise AND of the corresponding elements from x1 and x2.

    Precondition: All elements are non-negative (to simplify the specification)
    
    Postcondition: 
    1. For non-negative integers, each element of the result is the bitwise AND 
       of corresponding inputs
    2. The result preserves the mathematical properties of bitwise AND:
       - Commutativity: x & y = y & x
       - Associativity: (x & y) & z = x & (y & z)
       - Identity: x & (2^k - 1) = x for x < 2^k (all 1s acts as identity)
       - Annihilator: x & 0 = 0
       - Idempotence: x & x = x
    3. The result is always less than or equal to both inputs (for non-negative integers)
    4. Each bit in the result is 1 iff both corresponding bits in the inputs are 1
-/
theorem bitwise_and_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_nonneg : ∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x1.get i ≥ 0 ∧ x2.get i ≥ 0⌝⦄
    bitwise_and x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.toNat (x1.get i) &&& Int.toNat (x2.get i))) ∧
                (∀ i : Fin n, result.get i ≥ 0) ∧
                (∀ i : Fin n, result.get i ≤ x1.get i) ∧
                (∀ i : Fin n, result.get i ≤ x2.get i) ∧
                (∀ i : Fin n, result.get i = 0 ↔ (x1.get i = 0 ∨ x2.get i = 0)) ∧
                (∀ i : Fin n, x1.get i = x2.get i → result.get i = x1.get i)⌝⦄ := by
  intro h
  rw [bitwise_and_result]
  simp [bind_pure, pure_bind, map_pure]
  constructor
  · intro i
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Vector.get_mk]
  constructor
  · intro i
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Int.ofNat_nonneg]
  constructor
  · intro i
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Vector.get_mk]
    have h1 := (h i).1
    have h2 := (h i).2
    rw [← int_tonat_ofnat_nonneg (x1.get i) h1]
    simp [Int.ofNat_le_ofNat]
    exact nat_and_le_left _ _
  constructor
  · intro i
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Vector.get_mk]
    have h1 := (h i).1
    have h2 := (h i).2
    rw [← int_tonat_ofnat_nonneg (x2.get i) h2]
    simp [Int.ofNat_le_ofNat]
    exact nat_and_le_right _ _
  constructor
  · intro i
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Vector.get_mk]
    have h1 := (h i).1
    have h2 := (h i).2
    constructor
    · intro hz
      simp [Int.ofNat_eq_zero] at hz
      have : Int.toNat (x1.get i) = 0 ∨ Int.toNat (x2.get i) = 0 := by
        by_contra h_contra
        push_neg at h_contra
        cases' Nat.eq_zero_or_pos (Int.toNat (x1.get i)) with h_zero h_pos
        · contradiction
        · cases' Nat.eq_zero_or_pos (Int.toNat (x2.get i)) with h_zero2 h_pos2
          · contradiction
          · have : Int.toNat (x1.get i) &&& Int.toNat (x2.get i) = 0 := hz
            rw [Nat.land_eq_zero_iff] at this
            cases this with
            | inl h_left => exact h_contra.1 h_left
            | inr h_right => exact h_contra.2 h_right
      cases this with
      | inl h_left => 
        left
        rw [← int_tonat_ofnat_nonneg (x1.get i) h1]
        simp [Int.ofNat_eq_zero]
        exact h_left
      | inr h_right =>
        right
        rw [← int_tonat_ofnat_nonneg (x2.get i) h2]
        simp [Int.ofNat_eq_zero]
        exact h_right
    · intro hz
      simp [Int.ofNat_eq_zero]
      cases hz with
      | inl h_left =>
        rw [int_tonat_ofnat_nonneg (x1.get i) h1] at h_left
        simp [Int.toNat_eq_zero] at h_left
        have : Int.toNat (x1.get i) = 0 := by
          rw [Int.toNat_eq_zero]
          left; exact h_left
        simp [this]
      | inr h_right =>
        rw [int_tonat_ofnat_nonneg (x2.get i) h2] at h_right
        simp [Int.toNat_eq_zero] at h_right
        have : Int.toNat (x2.get i) = 0 := by
          rw [Int.toNat_eq_zero]
          left; exact h_right
        simp [this]
  · intro i h_eq
    simp [Vector.get_mk]
    have : i.val < min x1.toList.length x2.toList.length := by
      simp [Vector.toList_length]
      exact i.isLt
    rw [list_get_zipwith]
    simp [Vector.get_mk]
    have h1 := (h i).1
    rw [h_eq]
    rw [← int_tonat_ofnat_nonneg (x2.get i) (h i).2]
    simp [Int.ofNat_inj]
    exact nat_and_self _