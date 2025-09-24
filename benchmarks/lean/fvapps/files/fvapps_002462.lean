-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (n m : Nat) := Fin n → Fin m → Nat

def generate_eye_matrix (n m : Nat) : Matrix n m := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eye_matrix_valid_dimensions {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  ∃ (M : Matrix n m), M = generate_eye_matrix n m := sorry

theorem eye_matrix_diagonal_ones {n m : Nat} (h1 : n > 0) (h2 : m > 0) 
  (i : Fin n) (h3 : i.val < m) :
  (generate_eye_matrix n m) i ⟨i.val, h3⟩ = 1 := sorry

theorem eye_matrix_off_diagonal_zeros {n m : Nat} (h1 : n > 0) (h2 : m > 0)
  (i : Fin n) (j : Fin m) :
  i.val ≠ j.val → (generate_eye_matrix n m) i j = 0 := sorry

theorem eye_matrix_invalid_input {n m : Int} :
  n < 0 ∨ m < 0 → generate_eye_matrix n.natAbs m.natAbs = λ i j => 0 := sorry
-- </vc-theorems>