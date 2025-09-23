-- <vc-preamble>
def even_magic (n : Nat) : Array (Array Nat) := sorry

theorem even_magic_dimensions {n : Nat} (h : n ≥ 4) (h2 : n % 2 = 0) :
  let result := even_magic n
  result.size = n ∧ 
  ∀ i, i < n → (result.get ⟨i, by sorry⟩).size = n := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_position_pattern (matrix : Array (Array Nat)) (x y : Nat) (hx : x < matrix.size) (hy : y < matrix.size) : Prop := 
  let val := (matrix.get ⟨y, hy⟩).get ⟨x, by sorry⟩
  if x % 4 = y % 4 ∨ (x % 4 + y % 4) % 4 = 3
  then val = matrix.size * matrix.size - (y * matrix.size + x)
  else val = y * matrix.size + x + 1
-- </vc-definitions>

-- <vc-theorems>
theorem even_magic_contains_all_numbers {n : Nat} (h : n ≥ 4) (h2 : n % 2 = 0) :
  let result := even_magic n
  let flattened := result.flatten
  ∀ k, 1 ≤ k → k ≤ n*n → k ∈ flattened.toList := sorry

theorem even_magic_pattern {n : Nat} (h : n ≥ 4) (h2 : n % 2 = 0) :
  let result := even_magic n
  ∀ x y (hx : x < n) (hy : y < n), 
    check_position_pattern result x y (by sorry) (by sorry) := sorry
-- </vc-theorems>