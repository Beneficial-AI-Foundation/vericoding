import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Sign function for individual integers
def int_sign (x : Int) : Int :=
  if x > 0 then 1 else if x = 0 then 0 else -1

-- LLM HELPER: Properties of int_sign
lemma int_sign_pos (x : Int) (h : x > 0) : int_sign x = 1 := by
  unfold int_sign
  simp [h]

lemma int_sign_zero (x : Int) (h : x = 0) : int_sign x = 0 := by
  unfold int_sign
  simp [h]

lemma int_sign_neg (x : Int) (h : x < 0) : int_sign x = -1 := by
  unfold int_sign
  simp [not_lt.mpr (le_of_lt h)]
  exact ne_of_lt h
-- </vc-helpers>

-- <vc-definitions>
def sign {n : Nat} (a : Vector Int n) : Vector Int n :=
a.map int_sign
-- </vc-definitions>

-- <vc-theorems>
theorem sign_spec {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n ∧
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) :=
⟨by simp [sign, Vector.toList_map], by
  intro i
  constructor
  · intro h_pos
    simp [sign, Vector.get_map]
    exact int_sign_pos (a[i]) h_pos
  constructor
  · intro h_zero
    simp [sign, Vector.get_map]
    exact int_sign_zero (a[i]) h_zero
  · intro h_neg
    simp [sign, Vector.get_map]
    exact int_sign_neg (a[i]) h_neg⟩
-- </vc-theorems>
