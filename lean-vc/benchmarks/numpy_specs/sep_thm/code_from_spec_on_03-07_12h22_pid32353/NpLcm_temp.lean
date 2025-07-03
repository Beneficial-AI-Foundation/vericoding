/-
# NumPy LCM Specification

Port of np_lcm.dfy to Lean 4
-/

namespace DafnySpecs.NpLcm

/- LLM HELPER -/
def gcdInt (a b : Int) : Int :=
  if a = 0 then Int.natAbs b
  else if b = 0 then Int.natAbs a
  else Int.gcd (Int.natAbs a) (Int.natAbs b)

/-- Helper function for computing LCM of two integers -/
def lcmInt (a b : Int) : Int := 
  if a = 0 || b = 0 then 0
  else (Int.natAbs a * Int.natAbs b) / gcdInt a b

/-- Element-wise least common multiple of two vectors -/
def lcm {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i : Fin n => lcmInt (a[i]) (b[i]))

/- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/-- Specification: Output length equals input length -/
theorem lcm_length {n : Nat} (a b : Vector Int n) :
  (lcm a b).toList.length = n := by
  simp [lcm]
  exact vector_ofFn_length _

/- LLM HELPER -/
lemma lcmInt_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lcmInt a b := by
  simp [lcmInt]
  by_cases h1 : a = 0
  · simp [h1]
  · by_cases h2 : b = 0
    · simp [h2]
    · simp [h1, h2]
      apply Int.div_nonneg
      · apply Int.mul_nonneg
        · exact Int.natAbs_nonneg a
        · exact Int.natAbs_nonneg b
      · exact Int.natAbs_nonneg (gcdInt a b)

/-- Specification: Non-negative inputs requirement -/
theorem lcm_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (lcm a b)[i] := by
  intro i
  simp [lcm, Vector.ofFn]
  exact lcmInt_nonneg (a[i]) (b[i]) (ha i) (hb i)

/-- Specification: Element-wise LCM computation -/
theorem lcm_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (lcm a b)[i] = lcmInt (a[i]) (b[i]) := by
  intro i
  simp [lcm, Vector.ofFn]

end DafnySpecs.NpLcm