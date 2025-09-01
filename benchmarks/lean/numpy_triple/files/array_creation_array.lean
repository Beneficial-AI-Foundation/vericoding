/-  Create an array from existing data. This is the primary array creation function.
    Takes a list of Float elements and creates a Vector of the same length. -/

/-  Specification: array creates a vector containing exactly the input data elements
    in the same order. The result has the same length as the input list and preserves
    all elements at their corresponding indices. This captures the fundamental property
    of numpy.array - converting sequence-like data into array format while preserving
    element values and order. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def array (data : List Float) : Id (Vector Float data.length) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem array_spec (data : List Float) :
    ⦃⌜True⌝⦄
    array data
    ⦃⇓result => ⌜∀ i : Fin data.length, result.get i = data.get i⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
