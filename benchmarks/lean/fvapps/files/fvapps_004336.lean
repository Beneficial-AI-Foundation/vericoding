-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdMatrix (a : List Nat) (b : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcdMatrix_bounds {a b : List Nat} (ha : ∀ x ∈ a, x > 0) (hb : ∀ x ∈ b, x > 0) :
  ∃ min max : Nat,
    (∀ x ∈ a, ∀ y ∈ b, Nat.gcd x y ≥ min) ∧ 
    (∀ x ∈ a, ∀ y ∈ b, Nat.gcd x y ≤ max) ∧
    min ≤ gcdMatrix a b ∧ gcdMatrix a b ≤ max :=
  sorry

theorem gcdMatrix_positive {a b : List Nat} (ha : ∀ x ∈ a, x > 0) (hb : ∀ x ∈ b, x > 0) :
  gcdMatrix a b > 0 :=
  sorry

theorem gcdMatrix_identical_inputs {a b : List Nat} (ha : ∀ x ∈ a, x = List.head! a)
  (hb : ∀ x ∈ b, x = List.head! b) (heq : List.head! a = List.head! b) :
  gcdMatrix a b = List.head! a :=
  sorry

theorem gcdMatrix_multiples {a b : List Nat} (ha : List.length a = 1)
  (hb : ∀ y ∈ b, y % List.head! a = 0) :
  gcdMatrix a b = List.head! a :=
  sorry

theorem gcdMatrix_coprime : gcdMatrix [2,3,5,7] [11,13,17,19] = 1 :=
  sorry
-- </vc-theorems>