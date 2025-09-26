import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Nat

/-- A max on Int avoiding clashes with global `max`. -/
def intMax (x y : Int) : Int := if x ≥ y then x else y

lemma le_intMax_left (x y : Int) : x ≤ intMax x y := by
  unfold intMax
  by_cases h : x ≥ y
  · simp [h]
  ·
    have : x ≤ y := le_of_lt (lt_of_not_ge h)
    simpa [h] using this

lemma le_intMax_right (x y : Int) : y ≤ intMax x y := by
  unfold intMax
  by_cases h : x ≥ y
  · have : y ≤ x := h
    simpa [h] using this
  · simp [h]

/-- Maximum of the prefix of an array of given length `n`.
    For `n = 0` it is `0`. For `n = 1` it is `a[0]!`.
    For `n ≥ 2` it folds with `intMax` over indices `0..n-1`. -/
def prefixMax (a : Array Int) : Nat → Int
| 0 => 0
| (n+1) =>
  match n with
  | 0 => a[0]!
  | k+1 => intMax (prefixMax a (k+1)) (a[k+1]!)

lemma prefixMax_one (a : Array Int) : prefixMax a 1 = a[0]! := by
  simp [prefixMax]

lemma prefixMax_succ_succ (a : Array Int) (k : Nat) :
  prefixMax a (k+2) = intMax (prefixMax a (k+1)) (a[k+1]!) := by
  simp [prefixMax]

/-- Every in-bounds element of the prefix is bounded by `prefixMax`. -/
lemma get_le_prefixMax (a : Array Int) :
  ∀ n j, j < n → a[j]! ≤ prefixMax a n
| 0, j, hj => False.elim ((Nat.not_lt_zero _) hj)
| 1, j, hj =>
    by
      have hj0 : j = 0 := Nat.lt_one_iff.mp hj
      subst hj0
      simp [prefixMax_one]
| k+2, j, hj =>
    by
      have hle : j ≤ k+1 := Nat.lt_succ_iff.mp hj
      cases Nat.eq_or_lt_of_le hle with
      | inl h_eq =>
        subst h_eq
        simpa [prefixMax_succ_succ] using
          (le_intMax_right (prefixMax a (k+1)) (a[k+1]!))
      | inr h_lt =>
        have ih := get_le_prefixMax a (k+1) j h_lt
        have ih' : a[j]! ≤ intMax (prefixMax a (k+1)) (a[k+1]!) :=
          le_trans ih (le_intMax_left _ _)
        simpa [prefixMax_succ_succ] using ih'

/-- If the prefix length is positive, `prefixMax` is equal to some element in the prefix. -/
lemma exists_eq_prefixMax_of_pos (a : Array Int) :
  ∀ n, 0 < n → ∃ j, j < n ∧ prefixMax a n = a[j]!
| 0, h => False.elim ((lt_irrefl _) h)
| 1, _ => by
    exact ⟨0, Nat.zero_lt_one, by simp [prefixMax_one]⟩
| k+2, _ => by
    obtain ⟨j0, hj0, hj0eq⟩ := exists_eq_prefixMax_of_pos a (k+1) (Nat.succ_pos _)
    by_cases hcmp : prefixMax a (k+1) ≥ a[k+1]!
    · refine ⟨j0, Nat.lt_trans hj0 (Nat.lt_succ_self _), ?_⟩
      have hstep : prefixMax a (k+2) = prefixMax a (k+1) := by
        simp [prefixMax_succ_succ, intMax, hcmp]
      simpa [hstep, hj0eq]
    · refine ⟨k+1, Nat.lt_succ_self _, ?_⟩
      simp [prefixMax_succ_succ, intMax, hcmp]

-- </vc-helpers>

-- <vc-definitions>
def max (a : Array Int) : Int :=
prefixMax a a.size
-- </vc-definitions>

-- <vc-theorems>
theorem max_spec (a : Array Int) :

-- First ensures clause: max is larger than anything in array

(∀ j:Nat, 0 ≤ j ∧ j < a.size → max a ≥ a[j]!) ∧

-- Second ensures clause: if array non-empty, max exists in array

(a.size > 0 → ∃ j, 0 ≤ j ∧ j < a.size ∧ max a = a[j]!) :=
by
  constructor
  · intro j hj
    have hj_lt : j < a.size := hj.2
    have h := get_le_prefixMax a (a.size) j hj_lt
    change prefixMax a a.size ≥ a[j]!
    exact h
  · intro hpos
    obtain ⟨j, hj_lt, hEq⟩ := exists_eq_prefixMax_of_pos a (a.size) (by simpa using hpos)
    refine ⟨j, Nat.zero_le j, hj_lt, ?_⟩
    change prefixMax a a.size = a[j]!
    exact hEq
-- </vc-theorems>
