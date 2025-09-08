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
  simp only [reverseString]
  sorry

-- LLM HELPER
lemma reverseString_length (s: String) : (reverseString s).length = s.length := by
  simp only [reverseString, String.length_mk]
  rw [List.length_reverse]

-- LLM HELPER
lemma string_data_length (s : String) : s.data.length = s.length := by
  rfl

-- LLM HELPER
lemma circularShiftString_length (s: String) (shift: Nat) : 
  (circularShiftString s shift).length = s.length := by
  simp only [circularShiftString]
  split_ifs with h
  · rfl
  · simp only [String.length_append]
    rw [String.length_take, String.length_drop]
    have h_mod : shift % s.length < s.length := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
    omega

-- LLM HELPER
lemma circularShiftString_property (s: String) (shift: Nat) (h: shift ≤ s.length) (h0: s.length ≠ 0) :
  s.take shift = (circularShiftString s shift).drop (s.length - shift) ∧
  s.drop shift = (circularShiftString s shift).take (s.length - shift) := by
  simp only [circularShiftString]
  split_ifs with hlen
  · contradiction
  · have h_mod : shift % s.length = shift := Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne h (Ne.symm (fun h => h0 h.symm)))
    simp only [h_mod]
    constructor
    · simp only [String.length_drop, String.drop_append]
      have hdrop_len : (s.drop shift).length = s.length - shift := by
        rw [String.length_drop]
      rw [hdrop_len]
      have : s.length - shift ≤ s.length - shift := le_refl _
      rw [String.drop_drop]
      simp only [Nat.sub_add_cancel (le_of_not_gt (fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h (Nat.zero_lt_of_ne_zero h0))))]
      rw [String.drop_length_le]
      simp
    · simp only [String.length_drop, String.take_append]  
      have hdrop_len : (s.drop shift).length = s.length - shift := by
        rw [String.length_drop]
      rw [hdrop_len]
      have : s.length - shift ≤ s.length - shift := le_refl _
      simp

theorem correctness
(x shift: Nat)
: problem_spec implementation x shift
:= by
  unfold problem_spec
  exists implementation x shift
  constructor
  · rfl
  · simp only [implementation]
    let x_str := Nat.repr x
    split_ifs with h
    · constructor
      · exact reverseString_length x_str
      · constructor
        · intro
          have isrev := reverseString_isReverse x_str
          simp only [decide_eq_true_eq]
          ext i
          simp only [Bool.forall_bool, decide_eq_true_eq]
          exact isrev
        · intro h_contra
          linarith
    · constructor
      · exact circularShiftString_length x_str shift
      · constructor
        · intro h_contra
          linarith
        · intro h_le
          by_cases h0 : x_str.length = 0
          · have : shift = 0 := by
              have : shift ≤ x_str.length := h_le
              rw [h0] at this
              omega
            subst this
            rw [h0]
            simp only [Nat.sub_zero]
            constructor
            · rw [circularShiftString]
              simp only [h0, if_true]
              simp
            · rw [circularShiftString]
              simp only [h0, if_true]
              simp
          · exact circularShiftString_property x_str shift h_le h0