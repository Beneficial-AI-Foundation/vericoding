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
def reverseString (s: String) : String :=
  let chars := s.toList
  String.mk (chars.reverse)

-- LLM HELPER
def rotateLeft (s: String) (shift: Nat) : String :=
  let n := s.length
  if shift = 0 ∨ n = 0 then s
  else
    let shift_mod := shift % n
    s.drop shift_mod ++ s.take shift_mod

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  let n := x_str.length
  if n < shift then 
    reverseString x_str
  else
    rotateLeft x_str shift

-- LLM HELPER
lemma reverseString_length (s: String) : (reverseString s).length = s.length := by
  simp [reverseString]
  rw [String.length_mk]
  simp [List.length_reverse]

-- LLM HELPER
lemma reverseString_get (s: String) (i: Nat) (h: i < s.length) : 
  (reverseString s).get! ⟨i⟩ = s.get! ⟨s.length - 1 - i⟩ := by
  simp [reverseString]
  rw [String.get!_mk]
  simp [List.get_reverse]

-- LLM HELPER
lemma reverseString_isReverse (s: String) : 
  let n := (reverseString s).length;
  ∀ i, i < n / 2 → (reverseString s).get! ⟨i⟩ = (reverseString s).get! ⟨n - 1 - i⟩ := by
  intro i hi
  rw [reverseString_length]
  rw [reverseString_get, reverseString_get]
  simp

-- LLM HELPER
lemma rotateLeft_length (s: String) (shift: Nat) : (rotateLeft s shift).length = s.length := by
  simp [rotateLeft]
  split_ifs with h
  · rfl
  · rw [String.length_append, String.length_drop, String.length_take]
    simp [Nat.add_sub_cancel]

-- LLM HELPER
lemma rotateLeft_take_drop (s: String) (shift: Nat) (h: shift ≤ s.length) :
  s.take shift = (rotateLeft s shift).drop (s.length - shift) ∧
  s.drop shift = (rotateLeft s shift).take (s.length - shift) := by
  simp [rotateLeft]
  split_ifs with h1
  · cases h1 with
    | inl h2 => simp [h2]
    | inr h2 => simp [h2]
  · constructor
    · rw [String.drop_append]
      simp [String.length_drop]
      rw [Nat.sub_sub_self h]
      simp [String.drop_drop]
    · rw [String.take_append]
      simp [String.length_drop]
      rw [Nat.sub_sub_self h]
      simp

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift := by
  simp [problem_spec, implementation]
  let x_str := Nat.repr x
  let n := x_str.length
  use if n < shift then reverseString x_str else rotateLeft x_str shift
  constructor
  · rfl
  · simp [problem_spec]
    split_ifs with h
    · -- Case: n < shift
      constructor
      · exact reverseString_length x_str
      · constructor
        · intro; exact reverseString_isReverse x_str
        · intro h_contra
          exfalso
          exact Nat.lt_irrefl shift (Nat.lt_of_lt_of_le h h_contra)
    · -- Case: shift ≤ n
      constructor
      · exact rotateLeft_length x_str shift
      · constructor
        · intro h_contra
          exfalso
          exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h_contra (Nat.le_of_not_lt h))
        · intro h_le
          exact rotateLeft_take_drop x_str shift h_le