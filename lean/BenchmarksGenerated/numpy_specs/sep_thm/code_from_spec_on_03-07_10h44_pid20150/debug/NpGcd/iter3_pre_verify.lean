/-
# NumPy GCD Specification

Port of np_gcd.dfy to Lean 4
-/

namespace DafnySpecs.NpGcd

/-- Helper function for computing GCD of two integers -/
def gcdInt (a b : Int) : Int := Int.gcd a b

/-- Element-wise greatest common divisor of two vectors -/
def gcd {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.zipWith gcdInt a b

/- LLM HELPER -/
lemma vector_zipWith_length {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) :
  (Vector.zipWith f a b).toList.length = n := by
  simp [Vector.zipWith, Vector.toList_length]

/- LLM HELPER -/
lemma vector_zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (a : Vector α n) (b : Vector β n) (i : Fin n) :
  (Vector.zipWith f a b)[i] = f (a[i]) (b[i]) := by
  simp [Vector.zipWith_get']

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Int.gcd a b := by
  exact Int.gcd_nonneg a b

/-- Specification: Output length equals input length -/
theorem gcd_length {n : Nat} (a b : Vector Int n) :
  (gcd a b).toList.length = n := by
  unfold gcd
  exact vector_zipWith_length gcdInt a b

/-- Specification: Non-negative inputs requirement -/
theorem gcd_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (gcd a b)[i] := by
  intro i
  unfold gcd
  rw [vector_zipWith_get]
  unfold gcdInt
  exact int_gcd_nonneg (a[i]) (b[i]) (ha i) (hb i)

/-- Specification: Element-wise GCD computation -/
theorem gcd_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (gcd a b)[i] = gcdInt (a[i]) (b[i]) := by
  intro i
  unfold gcd
  exact vector_zipWith_get gcdInt a b i

end DafnySpecs.NpGcd