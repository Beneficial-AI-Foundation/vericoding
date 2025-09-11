-- <vc-preamble>
def generate_sierpinski_sequence (n : Nat) : List Nat :=
  sorry

def find_closest_value (m : Nat) : Nat := 
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_is_strictly_increasing {n : Nat} (h : 0 < n) (h2 : n ≤ 10000) :
  let seq := generate_sierpinski_sequence n
  ∀ i, i + 1 < seq.length → seq.get! i < seq.get! (i + 1) :=
sorry

theorem sequence_first_values {n : Nat} (h : 0 < n) (h2 : n ≤ 10000) :
  let seq := generate_sierpinski_sequence n
  seq.length ≥ 4 → seq.take 4 = [4, 13, 69, 130] :=
sorry

theorem closest_value_properties {m : Nat} (h : 0 < m) (h2 : m ≤ 10000) :
  let closest := find_closest_value m
  let seq := generate_sierpinski_sequence (m * 2)
  (closest ∈ seq) ∧ 
  (∀ x ∈ seq, abs (closest - m) ≤ abs (x - m)) ∧
  (∀ x ∈ seq, abs (x - m) = abs (closest - m) → x > m → closest ≥ x) :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_closest_value 1

/-
info: 5074
-/
-- #guard_msgs in
-- #eval find_closest_value 5000

/-
info: 14313
-/
-- #guard_msgs in
-- #eval find_closest_value 14313

/-
info: 18720
-/
-- #guard_msgs in
-- #eval find_closest_value 18332
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded