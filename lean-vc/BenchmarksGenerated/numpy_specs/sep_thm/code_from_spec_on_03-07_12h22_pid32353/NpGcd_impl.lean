/-
# NumPy GCD Specification

Port of np_gcd.dfy to Lean 4
-/

namespace DafnySpecs.NpGcd

/-- Helper function for computing GCD of two integers -/
def gcdInt (a b : Int) : Int := Int.gcd a b

/-- Element-wise greatest common divisor of two vectors -/
def gcd {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => gcdInt a[i] b[i])

/- LLM HELPER -/
lemma vector_ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

/- LLM HELPER -/
lemma int_gcd_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Int.gcd a b := by
  exact Int.gcd_nonneg a b

/-- Specification: Output length equals input length -/
theorem gcd_length {n : Nat} (a b : Vector Int n) :
  (gcd a b).toList.length = n := by
  simp [gcd]
  exact vector_ofFn_length _

/-- Specification: Non-negative inputs requirement -/
theorem gcd_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (gcd a b)[i] := by
  intro i
  simp [gcd, gcdInt]
  rw [vector_ofFn_get]
  exact int_gcd_nonneg (a[i]) (b[i]) (ha i) (hb i)

/-- Specification: Element-wise GCD computation -/
theorem gcd_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (gcd a b)[i] = gcdInt a[i] b[i] := by
  intro i
  simp [gcd]
  rw [vector_ofFn_get]

end DafnySpecs.NpGcd