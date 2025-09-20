-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_sierpinski_sequence (n : Nat) : List Nat :=
  sorry

def find_closest_value (m : Nat) : Nat :=
  sorry

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
-- </vc-theorems>