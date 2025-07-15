/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  let rec minAux (i : Nat) (currentMin : Int) : Int :=
    if hi : i < n then
      minAux (i + 1) (Int.min currentMin a[⟨i, hi⟩])
    else
      currentMin
  minAux 1 a[⟨0, h⟩]

/- LLM HELPER -/
lemma min_aux_le {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  ∀ j : Fin n, j.val < i → currentMin ≤ a[j] → 
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (Int.min m a[⟨k, hk⟩])
    else
      m
  minAux i currentMin ≤ a[j] := by
  intro j hj hle
  sorry

/- LLM HELPER -/
lemma min_aux_exists {n : Nat} (a : Vector Int n) (i : Nat) (currentMin : Int) :
  i ≤ n → (∃ j : Fin n, j.val < i ∧ currentMin = a[j]) →
  let rec minAux (k : Nat) (m : Int) : Int :=
    if hk : k < n then
      minAux (k + 1) (Int.min m a[⟨k, hk⟩])
    else
      m
  ∃ j : Fin n, minAux i currentMin = a[j] := by
  intro hi hexists
  sorry

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
    sorry
  · sorry

end DafnySpecs.NpMin