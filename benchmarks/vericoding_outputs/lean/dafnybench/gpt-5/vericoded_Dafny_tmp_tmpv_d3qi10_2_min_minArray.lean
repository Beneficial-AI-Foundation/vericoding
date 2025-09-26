import Mathlib
-- <vc-preamble>
def min_ (a b : Int) : Int :=
if a < b then a else b

def minFunction (a b : Int) : Int :=
if a < b then a else b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Classical

-- Helper lemmas about Nat.pred
lemma Nat.pred_lt_of_pos {n : Nat} (h : 0 < n) : Nat.pred n < n := by
  cases n with
  | zero => cases h
  | succ n =>
    simpa using Nat.lt_succ_self n

lemma le_pred_of_lt {k n : Nat} (hk : k < n) (hn : 0 < n) : k ≤ Nat.pred n := by
  cases n with
  | zero => cases hn
  | succ n =>
    simpa using Nat.le_of_lt_succ hk

lemma lt_of_le_pred_of_pos {k n : Nat} (hk : k ≤ Nat.pred n) (hn : 0 < n) : k < n := by
  cases n with
  | zero => cases hn
  | succ n =>
    simpa using Nat.lt_succ_of_le hk

-- Properties of min_
lemma min__le_left (a b : Int) : min_ a b ≤ a := by
  by_cases h : a < b
  · simp [min_, h]
  · have hb_le_a : b ≤ a := not_lt.mp h
    simpa [min_, h] using hb_le_a

lemma min__le_right (a b : Int) : min_ a b ≤ b := by
  by_cases h : a < b
  · have ha_le_b : a ≤ b := le_of_lt h
    simpa [min_, h] using ha_le_b
  · simp [min_, h]

lemma min__eq_left_or_right (a b : Int) : min_ a b = a ∨ min_ a b = b := by
  by_cases h : a < b
  · exact Or.inl (by simp [min_, h])
  · exact Or.inr (by simp [min_, h])

-- Prefix minimum over indices [0..i]
def prefixMin (a : Array Int) : (i : Nat) → i < a.size → Int
| 0, _ => a[0]!
| (Nat.succ j), h =>
  have hj : j < a.size := Nat.lt_of_succ_lt h
  min_ (prefixMin a j hj) a[j.succ]!

-- Specification of prefixMin
 theorem prefixMin_spec (a : Array Int) (i : Nat) (hi : i < a.size) :
  (∀ k : Nat, k ≤ i → prefixMin a i hi ≤ a[k]!) ∧
  (∃ k : Nat, k ≤ i ∧ prefixMin a i hi = a[k]!) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      constructor
      · intro k hk
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        simp [prefixMin]
      · exact ⟨0, le_rfl, by simp [prefixMin]⟩
  | succ j ih =>
      intro hi
      have hj : j < a.size := Nat.lt_of_succ_lt hi
      rcases ih hj with ⟨ih_all, ih_ex⟩
      constructor
      · intro k hk
        have hk' : k ≤ j ∨ k = j + 1 := Nat.le_or_eq_of_le_succ hk
        cases hk' with
        | inl hk_le_j =>
            have hmin_le_left : min_ (prefixMin a j hj) (a[j.succ]!) ≤ prefixMin a j hj :=
              min__le_left _ _
            have htrans := le_trans hmin_le_left (ih_all k hk_le_j)
            simpa [prefixMin] using htrans
        | inr hk_eq =>
            subst hk_eq
            have hmin_le_right : min_ (prefixMin a j hj) (a[j.succ]!) ≤ a[j.succ]! :=
              min__le_right _ _
            simpa [prefixMin] using hmin_le_right
      ·
        have hpair := min__eq_left_or_right (prefixMin a j hj) (a[j.succ]!)
        cases hpair with
        | inl hEq =>
            rcases ih_ex with ⟨k, hk, hkEq⟩
            refine ⟨k, Nat.le_trans hk (Nat.le_succ j), ?_⟩
            have hEq' : min_ a[k]! a[j.succ]! = a[k]! := by
              simpa [hkEq] using hEq
            simp [prefixMin, hEq', hkEq]
        | inr hEq =>
            exact ⟨j+1, le_rfl, by simp [prefixMin, hEq]⟩
-- </vc-helpers>

-- <vc-definitions>
def minArray (a : Array Int) : Int :=
if h : 0 < a.size then prefixMin a (Nat.pred a.size) (Nat.pred_lt_of_pos h) else 0
-- </vc-definitions>

-- <vc-theorems>
theorem min_spec (a b : Int) :
(min_ a b ≤ a ∧ min_ a b ≤ b) ∧
(min_ a b = a ∨ min_ a b = b) :=
by
  classical
  by_cases hlt : a < b
  · have hle : a ≤ b := le_of_lt hlt
    constructor
    · constructor
      · simp [min_, hlt]
      · simpa [min_, hlt] using hle
    · exact Or.inl (by simp [min_, hlt])
  · have hle : b ≤ a := not_lt.mp hlt
    constructor
    · constructor
      · simpa [min_, hlt] using hle
      · simp [min_, hlt]
    · exact Or.inr (by simp [min_, hlt])

theorem minFunction_spec (a b : Int) :
(minFunction a b ≤ a ∧ minFunction a b ≤ b) ∧
(minFunction a b = a ∨ minFunction a b = b) :=
by
  simpa [minFunction, min_] using min_spec a b

theorem minArray_spec (a : Array Int) :
a.size > 0 →
(∀ k : Nat, k < a.size → minArray a ≤ a[k]!) ∧
(∃ k : Nat, k < a.size ∧ minArray a = a[k]!) :=
by
  intro hpos
  have hpos' : 0 < a.size := hpos
  have hmin_eq :
    minArray a = prefixMin a (Nat.pred a.size) (Nat.pred_lt_of_pos hpos') := by
    simp [minArray, hpos']
  constructor
  · intro k hk
    have hk_le : k ≤ Nat.pred a.size := le_pred_of_lt hk hpos'
    have hspec := (prefixMin_spec a (Nat.pred a.size) (Nat.pred_lt_of_pos hpos')).1
    have := hspec k hk_le
    simpa [hmin_eq] using this
  · have hspec := (prefixMin_spec a (Nat.pred a.size) (Nat.pred_lt_of_pos hpos')).2
    rcases hspec with ⟨k, hk_le, hkEq⟩
    have hk_lt : k < a.size := lt_of_le_pred_of_pos hk_le hpos'
    refine ⟨k, hk_lt, ?_⟩
    simpa [hmin_eq] using hkEq
-- </vc-theorems>
