/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let rec maxAux (i : Nat) (currentMax : Int) : Int :=
    if hi : i < n then
      maxAux (i + 1) (max currentMax a[⟨i, hi⟩])
    else
      currentMax
  maxAux 1 a[⟨0, h⟩]

/- LLM HELPER -/
lemma max_aux_ge_init {n : Nat} (a : Vector Int n) (i : Nat) (currentMax : Int) :
  currentMax ≤ max.maxAux a i currentMax := by
  unfold max.maxAux
  split_ifs with hi
  · apply le_trans
    · exact le_refl currentMax
    · simp only [le_max_left]
      apply max_aux_ge_init
  · exact le_refl currentMax

/- LLM HELPER -/
lemma max_aux_in_vector {n : Nat} (h : n > 0) (a : Vector Int n) (i : Nat) (currentMax : Int) 
  (h_current : ∃ j : Fin n, currentMax = a[j]) :
  ∃ j : Fin n, max.maxAux a i currentMax = a[j] := by
  unfold max.maxAux
  split_ifs with hi
  · apply max_aux_in_vector
    simp only [max_def]
    split_ifs with h_comp
    · exact ⟨⟨i, hi⟩, rfl⟩
    · exact h_current
  · exact h_current

/- LLM HELPER -/
lemma max_aux_ge_all {n : Nat} (a : Vector Int n) (i j : Nat) (currentMax : Int) 
  (h_current : ∀ k : Fin n, k.val < i → a[k] ≤ currentMax) (hj : j < n) :
  a[⟨j, hj⟩] ≤ max.maxAux a i currentMax := by
  unfold max.maxAux
  split_ifs with hi
  · by_cases h : j < i
    · apply le_trans (h_current ⟨j, hj⟩ h)
      simp only [le_max_left]
      apply max_aux_ge_init
    · by_cases h' : j = i
      · simp only [h', le_max_right]
        apply max_aux_ge_init
      · have : j > i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt h) (Ne.symm h')
        apply max_aux_ge_all
        intro k hk
        by_cases hk' : k.val < i
        · exact le_trans (h_current k hk') (le_max_left _ _)
        · have : k.val = i := Nat.eq_of_le_of_lt_succ (Nat.le_of_not_gt hk') hk
          simp only [this, le_max_right]
  · exact h_current ⟨j, hj⟩ (Nat.not_lt.mp hi)

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  unfold max
  apply max_aux_in_vector
  exact ⟨⟨0, h⟩, rfl⟩

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  unfold max
  apply max_aux_ge_all
  intro k hk
  have : k.val = 0 := Nat.eq_of_lt_succ_of_not_lt hk (Nat.not_lt_zero _)
  simp only [this]
  exact le_refl _

end DafnySpecs.NpMax