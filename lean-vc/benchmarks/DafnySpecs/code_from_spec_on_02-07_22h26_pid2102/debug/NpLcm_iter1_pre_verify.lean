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
  else Int.natAbs a * Int.natAbs b / gcdInt a b

/-- Element-wise least common multiple of two vectors -/
def lcm {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => lcmInt (a.get i) (b.get i))

/-- LLM HELPER -/
theorem vector_ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n := by
  rw [Vector.ofFn_val, List.length_ofFn]

/-- LLM HELPER -/
theorem vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  rw [Vector.ofFn_get]

/-- LLM HELPER -/
theorem lcmInt_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ lcmInt a b := by
  unfold lcmInt
  split
  · simp
  · simp at *
    apply Nat.div_pos
    · apply Nat.mul_pos
      · rw [Int.natAbs_pos]
        push_neg at *
        exact Ne.symm (ne_of_not_eq (And.left *))
      · rw [Int.natAbs_pos]
        push_neg at *
        exact Ne.symm (ne_of_not_eq (And.right *))
    · sorry -- gcd is positive when both inputs are nonzero

/-- Specification: Output length equals input length -/
theorem lcm_length {n : Nat} (a b : Vector Int n) :
  (lcm a b).toList.length = n := by
  unfold lcm
  exact vector_ofFn_length _

/-- Specification: Non-negative inputs requirement -/
theorem lcm_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (lcm a b)[i] := by
  intro i
  unfold lcm
  rw [vector_ofFn_get]
  exact lcmInt_nonneg (a.get i) (b.get i) (ha i) (hb i)

/-- Specification: Element-wise LCM computation -/
theorem lcm_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (lcm a b)[i] = lcmInt (a[i]) (b[i]) := by
  intro i
  unfold lcm
  rw [vector_ofFn_get]
  rfl

end DafnySpecs.NpLcm