import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def reverseString (s: String) : String :=
  String.mk (s.data.reverse)

-- LLM HELPER
def circularShiftString (s: String) (shift: Nat) : String :=
  if s.length = 0 then s
  else
    let n := s.length
    let normalizedShift := shift % n
    let left := s.drop normalizedShift
    let right := s.take normalizedShift
    left ++ right

def implementation (x shift: Nat) : String :=
  let x_str := Nat.repr x
  if x_str.length < shift then
    reverseString x_str
  else
    circularShiftString x_str shift

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
lemma reverseString_isReverse (s: String) : 
  let n := s.length
  ∀ i, i < n / 2 → (reverseString s).get! ⟨i⟩ = (reverseString s).get! ⟨n - 1 - i⟩ := by
  intro i hi
  rfl

-- LLM HELPER
lemma reverseString_length (s: String) : (reverseString s).length = s.length := by
  rfl

-- LLM HELPER
lemma circularShiftString_length (s: String) (shift: Nat) : 
  (circularShiftString s shift).length = s.length := by
  simp [circularShiftString]
  split_ifs with h
  · rfl
  · simp [String.length_append]

-- LLM HELPER
lemma circularShiftString_property (s: String) (shift: Nat) (h: shift ≤ s.length) :
  s.take shift = (circularShiftString s shift).drop (s.length - shift) ∧
  s.drop shift = (circularShiftString s shift).take (s.length - shift) := by
  simp [circularShiftString]
  split_ifs with h0
  · exfalso
    have : s.length > 0 := Nat.pos_of_ne_zero (fun hc => by simp [hc] at h)
    linarith
  · constructor
    · rfl
    · rfl

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:= by
  unfold problem_spec
  exists implementation x shift
  constructor
  · rfl
  · simp [implementation]
    let x_str := Nat.repr x
    split_ifs with h
    · constructor
      · exact reverseString_length x_str
      · constructor
        · intro
          exact reverseString_isReverse x_str
        · intro h_contra
          linarith
    · constructor
      · exact circularShiftString_length x_str shift
      · constructor
        · intro h_contra
          linarith
        · intro h_le
          exact circularShiftString_property x_str shift h_le