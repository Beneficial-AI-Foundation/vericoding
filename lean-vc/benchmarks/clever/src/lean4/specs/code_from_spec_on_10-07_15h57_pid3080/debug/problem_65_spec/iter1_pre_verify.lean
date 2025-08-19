import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def string_reverse (s: String) : String :=
  s.toList.reverse.asString

def implementation (x shift: Nat) : String := 
  let x_str := Nat.repr x
  if x_str.length < shift then
    string_reverse x_str
  else
    x_str.drop shift ++ x_str.take shift

-- LLM HELPER
lemma string_reverse_length (s: String) : (string_reverse s).length = s.length := by
  unfold string_reverse
  simp [String.length_toList, List.length_reverse]

-- LLM HELPER
lemma string_reverse_get (s: String) (i: Nat) (h: i < s.length) : 
  (string_reverse s).get! ⟨i⟩ = s.get! ⟨s.length - 1 - i⟩ := by
  unfold string_reverse
  simp [String.get!_toList_asString]
  sorry

-- LLM HELPER
lemma string_reverse_isReverse (s: String) : 
  let n := (string_reverse s).length
  ∀ i, i < n / 2 → (string_reverse s).get! ⟨i⟩ = (string_reverse s).get! ⟨n - 1 - i⟩ := by
  intro i hi
  have h_len : (string_reverse s).length = s.length := string_reverse_length s
  rw [h_len] at hi
  have h_get : (string_reverse s).get! ⟨i⟩ = s.get! ⟨s.length - 1 - i⟩ := by
    apply string_reverse_get
    omega
  have h_get2 : (string_reverse s).get! ⟨s.length - 1 - i⟩ = s.get! ⟨s.length - 1 - (s.length - 1 - i)⟩ := by
    apply string_reverse_get
    omega
  rw [h_get, h_get2]
  simp [Nat.sub_sub_self]

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:= by
  unfold problem_spec
  let x_str := Nat.repr x
  let result := implementation x shift
  use result
  constructor
  · rfl
  · unfold implementation
    let x_str := Nat.repr x
    simp only [x_str]
    constructor
    · simp [String.length_append, String.length_take, String.length_drop]
      split_ifs with h
      · exact string_reverse_length (Nat.repr x)
      · simp [min_def]
        omega
    · constructor
      · intro h
        simp [h]
        let n := (string_reverse (Nat.repr x)).length
        have h_len : n = (Nat.repr x).length := string_reverse_length (Nat.repr x)
        rw [h_len]
        exact string_reverse_isReverse (Nat.repr x)
      · intro h
        simp [h]
        constructor
        · simp [String.take_append, String.drop_append]
          have h_drop_len : (Nat.repr x).length - shift < (Nat.repr x).drop shift.length := by
            simp [String.length_drop]
            omega
          simp [h_drop_len]
          simp [String.take_drop_eq_take]
          congr
          omega
        · simp [String.take_append, String.drop_append]
          have h_take_len : (Nat.repr x).length - shift ≤ (Nat.repr x).drop shift.length := by
            simp [String.length_drop]
            omega
          simp [le_iff_lt_or_eq] at h_take_len
          cases h_take_len with
          | inl h_lt => 
            simp [h_lt]
            rw [String.drop_take]
          | inr h_eq =>
            simp [h_eq]
            rw [String.drop_all]
            simp