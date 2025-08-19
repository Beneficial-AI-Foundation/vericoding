import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
lemma replicate_length {T : Type} (n : Nat) (x : T) : (List.replicate n x).length = n := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, ih]

-- LLM HELPER
lemma replicate_get {T : Type} (n : Nat) (x : T) (i : Fin n) : 
    (List.replicate n x).get ⟨i.val, by rw [replicate_length]; exact i.isLt⟩ = x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases' i.val with j
    · simp [List.replicate, List.get]
    · simp [List.replicate, List.get]
      apply ih
      exact ⟨j, Nat.lt_of_succ_lt_succ i.isLt⟩

-- LLM HELPER
lemma List.toArray_length {T : Type} (l : List T) : l.toArray.size = l.length := by
  simp [List.toArray, Array.size]

def problem_spec {n : Nat} {T : Type} [OfNat T 1] (ones_like : Vector T n → Id (Vector T n)) (a : Vector T n) : Prop :=
  ⦃⌜True⌝⦄
  ones_like a
  ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1⌝⦄

/-- Return a vector of ones with the same length as the input vector.
    This is the 1D version of numpy.ones_like which creates a new vector
    filled with ones, having the same size as the input vector. -/
def implementation {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) : Id (Vector T n) :=
  pure ⟨(List.replicate n 1).toArray, by simp [List.toArray_length, replicate_length]⟩

theorem correctness {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) :
    problem_spec implementation a := by
  unfold problem_spec implementation
  apply Triple.pure
  simp [Vector.get]
  intro i
  have h : (List.replicate n 1).get ⟨i.val, by rw [replicate_length]; exact i.isLt⟩ = 1 := by
    exact replicate_get n 1 i
  simp [Array.get_eq_getElem, List.getElem_toArray]
  exact h