/-
# NumPy LCM Specification

Port of np_lcm.dfy to Lean 4
-/

namespace DafnySpecs.NpLcm

-- LLM HELPER
def gcdInt (a b : Int) : Int :=
  if a = 0 then Int.natAbs b
  else if b = 0 then Int.natAbs a
  else Int.gcd (Int.natAbs a) (Int.natAbs b)

/-- Helper function for computing LCM of two integers -/
def lcmInt (a b : Int) : Int :=
  if a = 0 ∨ b = 0 then 0
  else Int.natAbs (a * b) / gcdInt a b

/-- Element-wise least common multiple of two vectors -/
def lcm {n : Nat} (a b : Vector Int n) : Vector Int n :=
  Vector.ofFn (fun i : Fin n => lcmInt (a[i]) (b[i]))

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]

-- LLM HELPER
lemma lcmInt_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lcmInt a b := by
  simp [lcmInt]
  split_ifs with h
  · norm_num
  · simp only [Int.natAbs_of_nonneg ha, Int.natAbs_of_nonneg hb]
    apply Int.div_nonneg
    · apply Int.mul_nonneg ha hb
    · simp [gcdInt]
      split_ifs with h1 h2
      · exfalso
        simp [h1] at h
      · exfalso
        simp [h2] at h
      · apply Int.gcd_nonneg

/-- Specification: Output length equals input length -/
theorem lcm_length {n : Nat} (a b : Vector Int n) :
  (lcm a b).toList.length = n := by
  simp [lcm]
  exact vector_ofFn_length _

/-- Specification: Non-negative inputs requirement -/
theorem lcm_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (lcm a b)[i] := by
  intro i
  simp [lcm]
  rw [vector_ofFn_get]
  exact lcmInt_nonneg (a[i]) (b[i]) (ha i) (hb i)

/-- Specification: Element-wise LCM computation -/
theorem lcm_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (lcm a b)[i] = lcmInt (a[i]) (b[i]) := by
  intro i
  simp [lcm]
  exact vector_ofFn_get _ _

end DafnySpecs.NpLcm