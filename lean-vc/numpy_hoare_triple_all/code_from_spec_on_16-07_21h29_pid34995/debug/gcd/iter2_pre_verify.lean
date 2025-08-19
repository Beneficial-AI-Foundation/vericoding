import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.gcd",
  "description": "Returns the greatest common divisor of |x1| and |x2|",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.gcd.html",
  "doc": "Returns the greatest common divisor of |x1| and |x2|.",
  "code": "# Universal function (ufunc) implemented in C\n# Returns the greatest common divisor of |x1| and |x2|\n# This function is implemented as a compiled ufunc in NumPy's C extension modules.\n# It provides optimized element-wise operations with support for:\n# - Broadcasting\n# - Type casting and promotion  \n# - Output array allocation\n# - Where parameter for conditional operation\n# - Vectorized execution using SIMD instructions where available"
}
-/

/-- numpy.gcd: Returns the greatest common divisor of |x1| and |x2|, element-wise.
    
    The GCD is computed on the absolute values of the inputs. For two integers a and b,
    gcd(a, b) is the largest positive integer that divides both |a| and |b|.
    
    Special cases:
    - gcd(0, 0) = 0
    - gcd(a, 0) = |a| for any non-zero a
    - gcd(0, b) = |b| for any non-zero b
    
    Returns an array of the same shape as the broadcasted x1 and x2.
-/
def numpy_gcd {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  return Vector.ofFn (fun i => Int.ofNat (Int.gcd (x1.get i) (x2.get i)))

-- LLM HELPER
lemma int_gcd_eq_natabs_gcd (a b : Int) : Int.gcd a b = a.natAbs.gcd b.natAbs := by
  simp [Int.gcd]

-- LLM HELPER
lemma int_gcd_self_eq_natabs (a : Int) : Int.ofNat (Int.gcd a 0) = Int.natAbs a := by
  simp [Int.gcd, Int.natAbs]

-- LLM HELPER
lemma int_gcd_zero_self_eq_natabs (a : Int) : Int.ofNat (Int.gcd 0 a) = Int.natAbs a := by
  simp [Int.gcd, Int.natAbs]

-- LLM HELPER
lemma int_gcd_comm (a b : Int) : Int.gcd a b = Int.gcd b a := by
  simp [Int.gcd, Nat.gcd_comm]

-- LLM HELPER
lemma int_gcd_dvd_left (a b : Int) : Int.ofNat (Int.gcd a b) ∣ a := by
  simp [Int.gcd]
  exact Int.natAbs_dvd.mp (Int.natCast_dvd.mpr (Nat.gcd_dvd_left a.natAbs b.natAbs))

-- LLM HELPER
lemma int_gcd_dvd_right (a b : Int) : Int.ofNat (Int.gcd a b) ∣ b := by
  simp [Int.gcd]
  exact Int.natAbs_dvd.mp (Int.natCast_dvd.mpr (Nat.gcd_dvd_right a.natAbs b.natAbs))

-- LLM HELPER
lemma int_gcd_greatest (a b d : Int) : d ∣ a → d ∣ b → d ∣ Int.ofNat (Int.gcd a b) := by
  intro ha hb
  simp [Int.gcd]
  have h1 : Int.natAbs d ∣ a.natAbs := by
    rw [Int.natAbs_dvd]
    exact ha
  have h2 : Int.natAbs d ∣ b.natAbs := by
    rw [Int.natAbs_dvd]
    exact hb
  have h3 : Int.natAbs d ∣ a.natAbs.gcd b.natAbs := Nat.dvd_gcd h1 h2
  exact Int.natCast_dvd.mpr h3

/-- Specification: numpy.gcd returns a vector where each element is the
    greatest common divisor of the absolute values of the corresponding elements in x1 and x2.
    
    Precondition: True (gcd is defined for all integers)
    Postcondition: For all indices i, result[i] equals the GCD of x1[i] and x2[i],
    which is mathematically equivalent to the GCD of their absolute values.
    
    Mathematical properties verified:
    1. Correctness: result[i] = Int.gcd(x1[i], x2[i]) (uses Lean's built-in GCD function)
    2. Non-negativity: result[i] ≥ 0 (GCD is always non-negative)
    3. Equivalence to absolute values: gcd(a, b) = gcd(|a|, |b|)
    4. Special cases: gcd(0,0)=0, gcd(a,0)=|a|, gcd(0,b)=|b|
    5. Divisibility: gcd(a,b) divides both a and b
    6. Greatest property: any common divisor of a and b also divides gcd(a,b)
    7. Commutativity: gcd(a,b) = gcd(b,a)
-/
theorem numpy_gcd_spec {n : Nat} (x1 x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    numpy_gcd x1 x2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = Int.ofNat (Int.gcd (x1.get i) (x2.get i))) ∧
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 (∀ i : Fin n, Int.gcd (x1.get i) (x2.get i) = (x1.get i).natAbs.gcd (x2.get i).natAbs) ∧
                 (∀ i : Fin n, (x1.get i = 0 ∧ x2.get i = 0) → result.get i = 0) ∧
                 (∀ i : Fin n, (x1.get i ≠ 0 ∧ x2.get i = 0) → result.get i = Int.natAbs (x1.get i)) ∧
                 (∀ i : Fin n, (x1.get i = 0 ∧ x2.get i ≠ 0) → result.get i = Int.natAbs (x2.get i)) ∧
                 (∀ i : Fin n, result.get i ∣ (x1.get i) ∧ result.get i ∣ (x2.get i)) ∧
                 (∀ i : Fin n, ∀ (d : Int), d ∣ (x1.get i) → d ∣ (x2.get i) → d ∣ result.get i) ∧
                 (∀ i : Fin n, Int.gcd (x2.get i) (x1.get i) = Int.gcd (x1.get i) (x2.get i))⌝⦄ := by
  simp [numpy_gcd]
  apply conj
  · intro i
    simp [Vector.get, Vector.ofFn]
  · apply conj
    · intro i
      simp [Vector.get, Vector.ofFn]
      exact Int.natCast_nonneg _
    · apply conj
      · intro i
        exact int_gcd_eq_natabs_gcd _ _
      · apply conj
        · intro i ⟨h1, h2⟩
          simp [Vector.get, Vector.ofFn, h1, h2, Int.gcd]
        · apply conj
          · intro i ⟨h1, h2⟩
            simp [Vector.get, Vector.ofFn]
            rw [int_gcd_self_eq_natabs]
          · apply conj
            · intro i ⟨h1, h2⟩
              simp [Vector.get, Vector.ofFn]
              rw [int_gcd_zero_self_eq_natabs]
            · apply conj
              · intro i
                simp [Vector.get, Vector.ofFn]
                constructor
                · exact int_gcd_dvd_left _ _
                · exact int_gcd_dvd_right _ _
              · apply conj
                · intro i d ha hb
                  simp [Vector.get, Vector.ofFn]
                  exact int_gcd_greatest _ _ _ ha hb
                · intro i
                  exact int_gcd_comm _ _