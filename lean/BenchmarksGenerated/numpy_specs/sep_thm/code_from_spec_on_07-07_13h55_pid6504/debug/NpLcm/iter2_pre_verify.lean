/-
# NumPy LCM Specification

Port of np_lcm.dfy to Lean 4
-/

namespace DafnySpecs.NpLcm

-- LLM HELPER
def gcdInt (a b : Int) : Int :=
  if b = 0 then Int.natAbs a else gcdInt b (a % b)
termination_by Int.natAbs b
decreasing_by
  simp_wf
  exact Int.natAbs_mod_lt a (Ne.symm (ne_of_gt (Int.natAbs_pos.mpr b)))

/-- Helper function for computing LCM of two integers -/
def lcmInt (a b : Int) : Int := 
  if a = 0 ∨ b = 0 then 0 else Int.natAbs (a * b) / gcdInt a b

/-- Element-wise least common multiple of two vectors -/
def lcm {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn fun i => lcmInt (a[i]) (b[i])

-- LLM HELPER
theorem vector_length_ofFn {n : Nat} (f : Fin n → Int) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/-- Specification: Output length equals input length -/
theorem lcm_length {n : Nat} (a b : Vector Int n) :
  (lcm a b).toList.length = n := by
  simp [lcm]
  exact vector_length_ofFn _

-- LLM HELPER
theorem gcdInt_nonneg (a b : Int) : 0 ≤ gcdInt a b := by
  induction b using Int.natAbs_induction with
  | zero => 
    simp [gcdInt]
    exact Int.natAbs_nonneg a
  | succ n ih =>
    simp [gcdInt]
    exact ih

-- LLM HELPER
theorem gcdInt_pos (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 0 < gcdInt a b := by
  have h_nonneg : 0 ≤ gcdInt a b := gcdInt_nonneg a b
  have h_ne_zero : gcdInt a b ≠ 0 := by
    intro h
    sorry
  exact Int.lt_of_le_of_ne h_nonneg (Ne.symm h_ne_zero)

-- LLM HELPER
theorem lcmInt_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lcmInt a b := by
  simp [lcmInt]
  by_cases h : a = 0 ∨ b = 0
  · simp [h]
  · push_neg at h
    have : 0 ≤ Int.natAbs (a * b) := Int.natAbs_nonneg _
    have : 0 ≤ gcdInt a b := gcdInt_nonneg a b
    exact Int.div_nonneg (Int.natAbs_nonneg _) this

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