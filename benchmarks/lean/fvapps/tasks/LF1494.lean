-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern_triangle (k : Nat) : List String := sorry

theorem pattern_triangle_symmetry (k : Nat) :
  pattern_triangle k = (pattern_triangle k).reverse := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_triangle_length (k : Nat) :
  (pattern_triangle k).length = 2 * k + 1 := sorry

theorem pattern_triangle_first_last (k : Nat) :
  (pattern_triangle k).head! = toString k ∧ 
  (pattern_triangle k).getLast! = toString k := sorry

theorem pattern_triangle_digits (k : Nat) : 
  ∀ s ∈ pattern_triangle k, (∀ c ∈ s.data, c.isDigit) := sorry

theorem pattern_triangle_middle_row (k : Nat) {h : k < (pattern_triangle k).length}: 
  let middle := (pattern_triangle k)[k]'h
  middle.take 1 = "0" ∧ 
  middle.takeRight 1 = toString k := sorry

theorem pattern_triangle_row_lengths_monotone (k : Nat) :
  let rows := pattern_triangle k
  let lens := rows.map String.length
  let mid := lens.length / 2
  (∀ i j, i < j → j < mid → i < lens.length → j < lens.length → lens[i]! ≤ lens[j]!) ∧
  (∀ i j, mid ≤ i → i < j → i < lens.length → j < lens.length → lens[i]! ≥ lens[j]!) := sorry

theorem pattern_triangle_zero :
  pattern_triangle 0 = ["0"] := sorry
-- </vc-theorems>