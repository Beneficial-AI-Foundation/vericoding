/-
# NumPy GCD Specification

Port of np_gcd.dfy to Lean 4
-/

namespace DafnySpecs.NpGcd

-- LLM HELPER
def gcdNat (a b : Nat) : Nat := Nat.gcd a b

-- LLM HELPER
lemma gcd_nonneg (a b : Nat) : 0 ≤ Int.ofNat (gcdNat a b) := by
  simp [gcdNat]

-- LLM HELPER
lemma int_natAbs_gcd (a b : Int) : Int.natAbs (Int.gcd a b) = Nat.gcd (Int.natAbs a) (Int.natAbs b) := by
  rw [Int.gcd_def]

-- LLM HELPER
lemma Int.gcd_nonneg (a b : Int) : 0 ≤ Int.gcd a b := by
  rw [Int.gcd_def]
  exact Int.coe_nat_nonneg _

-- LLM HELPER
lemma Vector.get_ofFn {n : Nat} {α : Type*} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  rfl

/-- Helper function for computing GCD of two integers -/
def gcdInt (a b : Int) : Int := Int.gcd a b

/-- Element-wise greatest common divisor of two vectors -/
def gcd {n : Nat} (a b : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => gcdInt (a[i]) (b[i]))

/-- Specification: Output length equals input length -/
theorem gcd_length {n : Nat} (a b : Vector Int n) :
  (gcd a b).toList.length = n := by
  simp [gcd, Vector.toList_ofFn]

/-- Specification: Non-negative inputs requirement -/
theorem gcd_nonneg_requirement {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, 0 ≤ (gcd a b)[i] := by
  intro i
  simp [gcd, Vector.get_ofFn]
  exact Int.gcd_nonneg (a[i]) (b[i])

/-- Specification: Element-wise GCD computation -/
theorem gcd_spec {n : Nat} (a b : Vector Int n)
  (ha : ∀ i : Fin n, 0 ≤ a[i])
  (hb : ∀ i : Fin n, 0 ≤ b[i]) :
  ∀ i : Fin n, (gcd a b)[i] = gcdInt (a[i]) (b[i]) := by
  intro i
  simp [gcd, Vector.get_ofFn, gcdInt]

end DafnySpecs.NpGcd