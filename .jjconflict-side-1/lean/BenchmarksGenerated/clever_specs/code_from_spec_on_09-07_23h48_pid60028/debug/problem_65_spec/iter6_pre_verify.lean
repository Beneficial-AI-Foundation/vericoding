def problem_spec
-- function signature
(implementation: Nat → Nat → String)
-- inputs
(x shift: Nat) :=
let isReverse (s: String) : Bool :=
  let n := s.length;
  ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
-- spec
let spec (result: String) :=
let x_str := Nat.repr x;
result.length = x_str.length ∧
(x_str.length < shift → isReverse x_str) ∧
(shift ≤ x_str.length →
  x_str.take shift = result.drop (x_str.length - shift) ∧
  x_str.drop shift = result.take (x_str.length - shift));
-- program termination
∃ result, implementation x shift = result ∧
spec result

-- LLM HELPER
def reverse_string (s: String) : String :=
  let chars := s.toList
  String.mk chars.reverse

-- LLM HELPER
def rotate_left (s: String) (shift: Nat) : String :=
  let len := s.length
  if shift ≤ len then
    s.drop shift ++ s.take shift
  else
    s

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  if x_str.length < shift then
    reverse_string x_str
  else
    rotate_left x_str shift

-- LLM HELPER
lemma reverse_string_length (s: String) : 
  (reverse_string s).length = s.length := by
  simp [reverse_string]

-- LLM HELPER
lemma reverse_string_isReverse (s: String) : 
  let n := s.length
  let rev := reverse_string s
  ∀ i, i < n / 2 → rev.get! ⟨i⟩ = rev.get! ⟨n - 1 - i⟩ := by
  intro i hi
  simp [reverse_string]
  sorry

-- LLM HELPER
lemma rotate_left_length (s: String) (shift: Nat) :
  (rotate_left s shift).length = s.length := by
  simp [rotate_left]
  split_ifs with h
  · simp [String.length_append]
  · rfl

-- LLM HELPER
lemma rotate_left_correct (s: String) (shift: Nat) (h: shift ≤ s.length) :
  let result := rotate_left s shift
  s.take shift = result.drop (s.length - shift) ∧
  s.drop shift = result.take (s.length - shift) := by
  constructor
  · simp [rotate_left, h]
    rw [String.drop_append]
    have h_len : s.length - shift ≤ (s.drop shift).length := by
      rw [String.length_drop]
      omega
    rw [String.drop_drop]
    simp
  · simp [rotate_left, h]
    rw [String.take_append]
    have h_len : s.length - shift ≤ (s.drop shift).length := by
      rw [String.length_drop]
      omega
    rw [String.take_left]
    simp

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift := by
  let x_str := Nat.repr x
  let result := implementation x shift
  let isReverse (s: String) : Bool :=
    let n := s.length;
    ∀ i, i < n / 2 → s.get! ⟨i⟩ = s.get! ⟨n - 1 - i⟩;
  let spec (result: String) :=
    result.length = x_str.length ∧
    (x_str.length < shift → isReverse x_str) ∧
    (shift ≤ x_str.length →
      x_str.take shift = result.drop (x_str.length - shift) ∧
      x_str.drop shift = result.take (x_str.length - shift));
  
  use result
  constructor
  · rfl
  · unfold implementation
    simp only [spec]
    split_ifs with h
    · constructor
      · exact reverse_string_length x_str
      · constructor
        · intro h_len
          exact reverse_string_isReverse x_str
        · intro h_shift
          exfalso
          exact Nat.not_le.mpr h h_shift
    · constructor
      · exact rotate_left_length x_str shift
      · constructor
        · intro h_len
          exfalso
          exact h h_len
        · intro h_shift
          exact rotate_left_correct x_str shift h_shift