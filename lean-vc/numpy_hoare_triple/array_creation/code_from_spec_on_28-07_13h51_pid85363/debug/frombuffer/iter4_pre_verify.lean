import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma offset_add_i_lt_n {n count offset : Nat} {i : Fin count} 
    (h : offset + count ≤ n) : offset + i.val < n := by
  have h_i_lt : i.val < count := i.isLt
  linarith

def problem_spec {n count : Nat} (impl : Vector UInt8 n → Nat → Nat → Id (Vector UInt8 count)) (buffer : Vector UInt8 n) (count' : Nat) (offset : Nat)
    (h_bounds : offset + count ≤ n) (h_offset : offset < n ∨ count = 0) : Prop :=
    ⦃⌜offset + count ≤ n ∧ (offset < n ∨ count = 0)⌝⦄
    impl buffer count' offset
    ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, offset_add_i_lt_n h_bounds⟩⌝⦄

/-- Interpret a buffer as a 1-dimensional array.
    Takes a buffer (represented as a Vector of bytes), the count of elements to read,
    and an offset (starting position in bytes) to create a Vector of the specified type.
    This models numpy.frombuffer which interprets raw bytes as typed array elements. -/
def frombuffer {n count : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  pure (Vector.ofFn fun i => buffer.get ⟨offset + i.val, by
    have h_i_lt : i.val < count := i.isLt
    exact Nat.add_lt_of_lt_sub_right h_i_lt
  ⟩)

theorem correctness {n count : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat)
    (h_bounds : offset + count ≤ n) (h_offset : offset < n ∨ count = 0) :
    problem_spec frombuffer buffer count h_bounds h_offset := by
  unfold problem_spec
  apply spec_pure
  intro h
  intro i
  simp [frombuffer, Vector.get_ofFn]