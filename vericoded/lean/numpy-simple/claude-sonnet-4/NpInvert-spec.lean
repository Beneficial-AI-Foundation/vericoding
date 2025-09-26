import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemma for Vector operations
lemma Vector.map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (v.map f).toList.length = n := by
  simp [Vector.map, Vector.toList]
-- </vc-helpers>

-- <vc-definitions>
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n :=
Vector.map (fun x => (2^bitWidth - 1) - x) a
-- </vc-definitions>

-- <vc-theorems>
theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] :=
⟨by exact Vector.map_length (fun x => (2^bitWidth - 1) - x) a,
 fun i => by simp [invert, Vector.get_map]⟩
-- </vc-theorems>
