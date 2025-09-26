import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper definitions needed for this problem
-- </vc-helpers>

-- <vc-definitions>
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n :=
  Vector.map (fun x => (2^bitWidth - 1) - x) a
-- </vc-definitions>

-- <vc-theorems>
theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] :=
by
  constructor
  · simp [invert]
  · intro i
    simp [invert, Vector.get_map]
-- </vc-theorems>
