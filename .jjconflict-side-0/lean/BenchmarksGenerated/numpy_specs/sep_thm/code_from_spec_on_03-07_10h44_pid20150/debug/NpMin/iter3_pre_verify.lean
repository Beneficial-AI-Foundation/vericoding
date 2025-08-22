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

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let rec minAux (i : Nat) (currentMin : Int) : Int :=
    if hi : i < n then
      minAux (i + 1) (minInt currentMin a[⟨i, hi⟩])
    else
      currentMin
  minAux 1 a[⟨0, h⟩]

/- LLM HELPER -/
lemma min_aux_le {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  ∀ j : Fin n, j.val < i → currentMin ≤ a[j] → 
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (minInt m a[⟨k, hk⟩])
    else
      m
  minAux i currentMin ≤ a[j] := by
  intro j hj hle
  induction i generalizing currentMin with
  | zero => 
    simp at hj
  | succ i ih =>
    simp [minAux]
    by_cases hi : i + 1 < n
    · simp [hi]
      apply ih
      · exact Nat.lt_of_lt_succ hj
      · exact hle
    · simp [hi]
      exact hle

/- LLM HELPER -/
lemma min_aux_exists {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  i ≤ n → (∃ j : Fin n, j.val < i ∧ currentMin = a[j]) →
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (minInt m a[⟨k, hk⟩])
    else
      m
  ∃ j : Fin n, minAux i currentMin = a[j] := by
  intro hi hexists
  induction' Nat.sub n i using Nat.strong_induction_on with d ih generalizing i currentMin
  simp [minAux]
  by_cases hik : i < n
  · simp [hik]
    have : n - (i + 1) < n - i := by
      simp [Nat.sub_succ]
      exact Nat.sub_lt (Nat.le_sub_of_add_le (Nat.add_le_of_le_sub hi (by simp))) (by simp)
    apply ih this
    · exact Nat.succ_le_of_lt hik
    · by_cases h : currentMin ≤ a[⟨i, hik⟩]
      · use ⟨i, hik⟩
        simp [minInt, h]
      · obtain ⟨j, hj⟩ := hexists
        use j
        simp [minInt, h]
        exact hj.2
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
  by_cases hi : i.val = 0
  · simp [hi]
    obtain ⟨j, hj⟩ := min_exists h a
    rw [hj]
    apply min_aux_le
    · simp
    · rfl
  · have : i.val ≥ 1 := by
      cases' i.val with k
      · contradiction
      · simp
    apply min_aux_le
    · exact this
    · rfl

end DafnySpecs.NpMin