-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiples (m : Nat) (n : Int) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiples_length {m : Nat} {n : Int} (h : m ≤ 1000) :
  (multiples m n).size = m := sorry

theorem multiples_sequence {m : Nat} {n : Int} (h1 : m ≤ 1000) (h2 : m > 0) :
  ∀ i : Nat, i < m → (multiples m n)[i]! = (i + 1) * n := sorry

theorem multiples_first {m : Nat} {n : Int} (h1 : m ≤ 1000) (h2 : m > 0) :
  (multiples m n)[0]! = n := sorry

theorem multiples_sign_preservation {m : Nat} {n : Int} (h1 : m ≤ 1000) (h2 : m > 0) :
  (n < 0 → ∀ x ∈ multiples m n, x < 0) ∧
  (n > 0 → ∀ x ∈ multiples m n, x > 0) ∧
  (n = 0 → ∀ x ∈ multiples m n, x = 0) := sorry
-- </vc-theorems>