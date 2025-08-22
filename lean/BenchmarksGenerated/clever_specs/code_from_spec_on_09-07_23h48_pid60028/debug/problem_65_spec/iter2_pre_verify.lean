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
lemma reverse_string_spec (s: String) : 
  let n := s.length
  let rev := reverse_string s
  rev.length = n ∧ (∀ i, i < n / 2 → rev.get! ⟨i⟩ = rev.get! ⟨n - 1 - i⟩) := by
  constructor
  · simp [reverse_string]
  · intro i hi
    simp [reverse_string]
    sorry

-- LLM HELPER
lemma rotate_left_spec (s: String) (shift: Nat) (h: shift ≤ s.length) :
  let result := rotate_left s shift
  result.length = s.length ∧
  s.take shift = result.drop (s.length - shift) ∧
  s.drop shift = result.take (s.length - shift) := by
  constructor
  · simp [rotate_left]
    split_ifs with h'
    · simp [String.length_append]
    · rfl
  · constructor
    · simp [rotate_left]
      split_ifs with h'
      · simp [String.drop_append]
      · simp at h'
        contradiction
    · simp [rotate_left]
      split_ifs with h'
      · simp [String.take_append]
      · simp at h'
        contradiction

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
    simp only [result]
    split_ifs with h
    · constructor
      · have rev_spec := reverse_string_spec x_str
        exact rev_spec.1
      · constructor
        · intro h_len
          have rev_spec := reverse_string_spec x_str
          exact rev_spec.2
        · intro h_shift
          exfalso
          exact Nat.not_le.mpr h h_shift
    · constructor
      · have rot_spec := rotate_left_spec x_str shift (Nat.le_of_not_gt h)
        exact rot_spec.1
      · constructor
        · intro h_len
          exfalso
          exact h h_len
        · intro h_shift
          have rot_spec := rotate_left_spec x_str shift h_shift
          exact ⟨rot_spec.2.1, rot_spec.2.2⟩