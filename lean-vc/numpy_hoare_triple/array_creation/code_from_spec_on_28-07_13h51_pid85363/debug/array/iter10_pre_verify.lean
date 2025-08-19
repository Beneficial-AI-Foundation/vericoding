import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Create an array from existing data. This is the primary array creation function.
    Takes a list of Float elements and creates a Vector of the same length. -/
def array (data : List Float) : Id (Vector Float data.length) :=
  pure (Vector.ofFn (fun i => data.get i))

-- LLM HELPER
lemma vector_ofFn_get (data : List Float) (i : Fin data.length) :
  (Vector.ofFn (fun j : Fin data.length => data.get j)).get i = data.get i := by
  simp [Vector.get_ofFn]

/-- Specification: array creates a vector containing exactly the input data elements
    in the same order. The result has the same length as the input list and preserves
    all elements at their corresponding indices. This captures the fundamental property
    of numpy.array - converting sequence-like data into array format while preserving
    element values and order. -/
def array_spec (data : List Float) :
    ⦃⌜True⌝⦄
    array data
    ⦃⇓result => ⌜∀ i : Fin data.length, result.get i = data.get i⌝⦄ := by
  unfold array
  simp only [pure]
  apply Hoare.spec_ret
  intro i
  exact vector_ofFn_get data i