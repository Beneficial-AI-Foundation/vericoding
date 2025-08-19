/-
# NumPy LCM Specification

Port of np_lcm.dfy to Lean 4
-/

namespace DafnySpecs.NpLcm

/-- LLM HELPER -/
def gcdInt (a b : Int) : Int :=
  if a = 0 then Int.natAbs b
  else if b = 0 then Int.natAbs a
  else Int.gcd (Int.natAbs a) (Int.natAbs b)

/-- Helper function for computing LCM of two integers -/
def lcmInt (a b : Int) : Int := 
  if a = 0 ∨ b = 0 then 0
  else (Int.natAbs a * Int.natAbs b) / gcdInt a b

/-- Element-wise least common multiple of two vectors -/
def lcm {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => lcmInt (a.get i) (b.get i))

/-- LLM HELPER -/
theorem gcdInt_pos (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < gcdInt a b := by
  unfold gcdInt
  by_cases h : a = 0
  · contradiction
  · simp [h]
    by_cases h' : b = 0
    · contradiction
    · simp [h']
      exact Int.gcd_pos_of_ne_zero_left (Int.natAbs_ne_zero.mpr h)

/-- LLM HELPER -/
theorem lcmInt_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lcmInt a b := by
  unfold lcmInt
  by_cases h : a = 0 ∨ b = 0
  · simp [h]
  · simp [h]
    apply Int.div_nonneg_of_nonneg
    apply Int.mul_nonneg
    · exact Int.natAbs_nonneg a
    · exact Int.natAbs_nonneg b

/-- Specification: Output length equals input length -/
theorem lcm_length {n : Nat} (a b : Vector Int n) :
  (lcm a b).toList.length = n := by
  unfold lcm
  simp [Vector.toList_ofFn]

/-- Specification: Non-negative inputs requirement -/
theorem lcm_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (lcm a b)[i] := by
  intro i
  unfold lcm
  simp [Vector.ofFn_get]
  exact lcmInt_nonneg (a.get i) (b.get i) (ha i) (hb i)

/-- Specification: Element-wise LCM computation -/
theorem lcm_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (lcm a b)[i] = lcmInt (a[i]) (b[i]) := by
  intro i
  unfold lcm
  simp [Vector.ofFn_get]

end DafnySpecs.NpLcm