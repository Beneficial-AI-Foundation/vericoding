/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/- LLM HELPER -/
def minInt (x y : Int) : Int := if x ≤ y then x else y

/- LLM HELPER -/
lemma minInt_le_left (x y : Int) : minInt x y ≤ x := by
  simp [minInt]
  by_cases h : x ≤ y
  · simp [h]
  · simp [h]

/- LLM HELPER -/
lemma minInt_le_right (x y : Int) : minInt x y ≤ y := by
  simp [minInt]
  by_cases h : x ≤ y
  · simp [h]; exact h
  · simp [h]

/- LLM HELPER -/
lemma minInt_eq_left_or_right (x y : Int) : minInt x y = x ∨ minInt x y = y := by
  simp [minInt]
  by_cases h : x ≤ y
  · simp [h]
  · simp [h]

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let rec minAux (i : Nat) (currentMin : Int) : Int :=
    if hi : i < n then
      minAux (i + 1) (minInt currentMin a[⟨i, hi⟩])
    else
      currentMin
  minAux 1 a[⟨0, h⟩]

/- LLM HELPER -/
lemma min_aux_bounded {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  i ≤ n → (∃ j : Fin n, currentMin = a[j]) →
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (minInt m a[⟨k, hk⟩])
    else
      m
  ∀ j : Fin n, minAux i currentMin ≤ a[j] := by
  intro hi hexists j
  induction' Nat.sub n i using Nat.strong_induction_on with d ih generalizing i currentMin
  simp only [minAux]
  by_cases hik : i < n
  · simp [hik]
    have : n - (i + 1) < n - i := by
      cases' Nat.eq_or_lt_of_le hi with h h
      · rw [h] at hik
        simp at hik
      · exact Nat.sub_succ_lt_self n i (Nat.sub_pos_of_lt h)
    apply ih this
    · exact Nat.succ_le_of_lt hik
    · have h_min := minInt_eq_left_or_right currentMin a[⟨i, hik⟩]
      cases' h_min with h_left h_right
      · rw [← h_left]
        exact hexists
      · rw [← h_right]
        use ⟨i, hik⟩
        simp
  · simp [hik]
    obtain ⟨k, hk⟩ := hexists
    rw [hk]
    have h_le : k.val < n := k.isLt
    simp

/- LLM HELPER -/
lemma min_aux_exists {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  i ≤ n → (∃ j : Fin n, currentMin = a[j]) →
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (minInt m a[⟨k, hk⟩])
    else
      m
  ∃ j : Fin n, minAux i currentMin = a[j] := by
  intro hi hexists
  induction' Nat.sub n i using Nat.strong_induction_on with d ih generalizing i currentMin
  simp only [minAux]
  by_cases hik : i < n
  · simp [hik]
    have : n - (i + 1) < n - i := by
      cases' Nat.eq_or_lt_of_le hi with h h
      · rw [h] at hik
        simp at hik
      · exact Nat.sub_succ_lt_self n i (Nat.sub_pos_of_lt h)
    apply ih this
    · exact Nat.succ_le_of_lt hik
    · have h_min := minInt_eq_left_or_right currentMin a[⟨i, hik⟩]
      cases' h_min with h_left h_right
      · rw [← h_left]
        exact hexists
      · rw [← h_right]
        use ⟨i, hik⟩
        simp
  · simp [hik]
    exact hexists

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] := by
  unfold min
  have h0 : (0 : Nat) < n := h
  apply min_aux_exists
  · simp
  · use ⟨0, h0⟩
    simp

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a[i] := by
  intro i
  unfold min
  have h0 : (0 : Nat) < n := h
  apply min_aux_bounded
  · simp
  · use ⟨0, h0⟩
    simp

end DafnySpecs.NpMin