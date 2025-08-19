import Mathlib
import BigNum.Defs
import BigNum.Convert

/-! # Correctness of mod related definitions.

Main results:

* Proof that the binary definition of a number with a power of two corresponds to a power of two
    `isPowTwo_iff`: `isPowTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k)`
* Proof that the bignum definition of mod to a power of two is correct (variant 1)
  `modPowTwoListBool_listBoolToNat`:
    `listBoolToNat (modPowTwoListBool as bs) = (listBoolToNat as) % (listBoolToNat bs)`
* Proof that the bignum definition of mod to a power of two is correct (variant 2)
    `modPowTwo_correct`: `strToNat (modPowTwo a b) = strToNat a % strToNat b`
* Proof that the bignum definition of mod to a power of two is correct (variant 3)
    `modPowTwo_correct'`: `strToNat (modPowTwo (natToStr m) (natToStr (2 ^ n))) = m % (2 ^ n)`
-/

@[simp]
lemma isZero_of_empty : isZero [] := by
  exact trivial

@[simp]
lemma isOne_of_true : isOne [true] := by
  exact trivial

@[simp]
lemma listBoolToNat_of_isZero (bs : List Bool) : isZero bs ↔ listBoolToNat bs = 0 := by
  constructor
  · intro h
    induction bs with
    | nil => rfl
    | cons head tail ih => by_cases head <;> simp_all [isZero]
  · intro h
    induction bs with
    | nil =>
      simp_all
    | cons head tail ih => by_cases head <;> simp_all [isZero]

@[simp]
lemma listBoolToNat_of_isOne (bs : List Bool) : isOne bs ↔ listBoolToNat bs = 1 := by
  constructor
  · intro h
    cases bs with
    | nil => simp [isOne] at h
    | cons head tail =>
      cases head with
      | true =>
        cases tail with
        | nil => simp
        | cons t_head t_tail => simp_all [isOne, isZero]
      | false => simp [isOne] at h
  · intro h
    cases bs with
    | nil => simp [isOne] at h
    | cons head tail =>
      cases head with
      | true =>
        cases tail with
        | nil => simp
        | cons t_head t_tail => simp_all [isOne, isZero]
      | false => simp [isOne] at h

lemma isZero_tail {tail : List Bool} (h : ∃ k, listBoolToNat (true :: tail) = 2 ^ k) :
    isZero tail := by
  induction tail with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨k, hk⟩ := h
    obtain hk' | hk' : k = 0 ∨ 0 < k := by omega
    · simp_all
    · have ho : Odd (2 ^ k) := by simp [← hk]
      have he : Even (2 ^ k) := by exact (Nat.even_pow' <| Nat.ne_zero_of_lt hk').mpr (by norm_num)
      -- Surely there is a lemma `Odd m → Even m → False` instead of the next two lines?
      simp [Odd, Even] at ho he
      omega

lemma isPowTwo_of_isPowTwo_tail {tail} (h : isPowTwo tail) : isPowTwo (false :: tail) := by
  simpa [isPowTwo]

theorem isPowTwo_iff (bs : List Bool) :
  isPowTwo bs ↔ (0 < listBoolToNat bs ∧ ∃ k, listBoolToNat bs = 2^k) := by
  constructor
  -- Forward direction
  · intro h
    induction bs with
    | nil => simp [isPowTwo] at h
    | cons head tail ih =>
      cases head with
      | true =>
        -- Case: bs = true :: tail
        refine ⟨by simp, Nat.size (listBoolToNat tail), ?_⟩
        simp_all [listBoolToNat, isPowTwo]
      | false =>
        -- Case: bs = false :: tail
        obtain ⟨k, hk⟩ := (ih h).2
        refine ⟨?_, k + 1, ?_⟩
        · simp_all [isPowTwo, listBoolToNat]
        · simp [hk]
          ring
  -- Reverse direction
  · intro ⟨h, hk⟩
    induction bs with
    | nil =>
      simp [listBoolToNat] at h
    | cons head tail ih =>
      cases head with
      | true =>
        -- Case: bs = true :: tail
        have := isZero_tail hk
        simp_all [isPowTwo]
      | false =>
        -- Case: bs = false :: tail
        have : 0 < listBoolToNat tail := by
          simp_all
        have := ih this
        obtain ⟨ℓ, hℓ⟩ : ∃ k, listBoolToNat tail = 2 ^ k := by
          obtain ⟨k, hk⟩ := hk
          obtain hc | hc : k = 0 ∨ 0 < k := by omega
          · simp_all
          · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := Nat.exists_eq_add_one.mpr hc
            use j
            simp_all  [hj, show 2 ^ (j + 1) = 2 * 2 ^ j by omega]
        apply isPowTwo_of_isPowTwo_tail
        simp_all

@[simp]
lemma modPowTwoListBool_of_empty {as : List Bool} : modPowTwoListBool as [] = as := by
  by_cases hc : as = [] <;> simp [hc, modPowTwoListBool]

@[simp]
lemma modPowTwoListBool_of_true {as bs} : modPowTwoListBool as (true :: bs) = [] := by
  by_cases hc : as = [] <;> simp [hc, modPowTwoListBool]

@[simp]
lemma isPowTwo_of_isPowTwo {tail} (h : isPowTwo (false :: tail)) : isPowTwo (tail) := by
  simp_all [isPowTwo]

@[simp]
lemma isZero_of_isPowTwo {tail} (h : isPowTwo (true :: tail)) : isZero tail := by
  exact h

-- Surprising that this isn't already available or easier to prove
/-- If `Even a` and `Even b` then `a < b` implies that `a + 2 ≤ b`. -/
lemma add_two_le_of_even_of_lt (a b : Nat) (ha : Even a) (hb : Even b) (h : a < b) : a + 2 ≤ b := by
  obtain ⟨k, hk⟩ := Even.exists_two_nsmul a ha
  obtain ⟨l, hl⟩ := Even.exists_two_nsmul b hb
  have : k + 1 ≤ l := by
    refine Order.add_one_le_iff.mpr ?_
    simp_all
  calc a + 2
  _ = 2 * k + 2 * 1 := by simp [hk]
  _ = 2 * (k + 1) := by ring
  _ ≤ 2 * l := by simp [this]
  _ = b := by simp [hl]

/-- Unexpected effect of natural number division for even numbers. -/
lemma div_even_add_one (A B : Nat) : 2 * A / (2 * B) = (2 * A + 1) / (2 * B) := by
  have := Nat.div_add_mod' (2 * A) (2 * B)
  by_cases hc : B = 0
  · simp [hc]
  · have := Nat.add_div (a := 2 * A) (b := 1) (c := 2 * B) (show 0 < 2 * B by omega)
    have : 1 / (2 * B) = 0 := by
      exact Nat.div_eq_of_lt (by omega)
    have : 1 % (2 * B) = 1 := by
      exact Nat.mod_eq_of_lt (by omega)
    have : 2 * A % (2 * B) + 1 < 2 * B := by
      refine add_two_le_of_even_of_lt (2 * A % (2 * B)) (2 * B) ?_ ?_ ?_
      · exact Even.mod_even (even_two_mul A) (even_two_mul B)
      · exact even_two_mul B
      · exact Nat.mod_lt (2 * A) (by omega)
    simp_all

-- Surprising that this isn't easier to prove, requires the above two lemmas in current formulation.
lemma simple_yet_seemingly_hard (A B : Nat) : 2 * (A % B) + 1 = (2 * A + 1) % (2 * B) := by
  have := Nat.mul_mod_mul_left 2 A B
  have := Nat.div_add_mod (2 * A) (2 * B)
  have h := Nat.div_add_mod (2 * A + 1) (2 * B)
  rw [← div_even_add_one A B] at h
  bound

lemma modPowTwoListBool_listBoolToNat (as bs : List Bool) (h : isPowTwo bs) :
    listBoolToNat (modPowTwoListBool as bs) = (listBoolToNat as) % (listBoolToNat bs) := by
  induction as, bs using modPowTwoListBool.induct with
    | case1 counter => simp [modPowTwoListBool]
    | case2 as has => simp
    | case3 ha ta tb ih =>
      specialize ih <| isPowTwo_of_isPowTwo h
      by_cases hc : ha
      · simp [hc, modPowTwoListBool, ih]
        have := simple_yet_seemingly_hard (listBoolToNat ta) (listBoolToNat tb)
        exact this
      · simpa [hc, modPowTwoListBool, ih] using
          (Nat.mul_mod_mul_left 2 (listBoolToNat ta) (listBoolToNat tb)).symm
    | case4 bs tail ht =>
      have := isZero_of_isPowTwo h
      have : listBoolToNat tail = 0 := by exact (listBoolToNat_of_isZero tail).mp h
      simp [modPowTwoListBool, this]
      exact Eq.symm (Nat.mod_one (listBoolToNat bs))

/-- BigNum modPowTwo coincides with `Nat` addition. -/
theorem modPowTwo_correct (a b : String) (h : isPowTwo' b) :
    strToNat (modPowTwo a b) = strToNat a % strToNat b := by
  simpa [modPowTwo, strToNat] using
    modPowTwoListBool_listBoolToNat (strToListBool a) (strToListBool b) (by exact h)

/-- BigNum modPowTwo coincides with `Nat` addition. -/
theorem modPowTwo_correct' (m n : Nat) :
    strToNat (modPowTwo (natToStr m) (natToStr (2 ^ n))) = m % (2 ^ n) := by
  have hn : isPowTwo' (natToStr (2 ^ n)) := by
    simp [isPowTwo', natToStr, (isPowTwo_iff <| natToListBool (2 ^ n)).mpr]
  simp [modPowTwo_correct (natToStr m) (natToStr (2 ^ n)) hn]
