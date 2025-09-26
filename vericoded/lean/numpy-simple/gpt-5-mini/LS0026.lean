import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def mask (bitWidth : Nat) : Nat := Nat.pow 2 bitWidth - 1

-- </vc-helpers>

-- <vc-definitions>
def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n :=
let m := mask bitWidth
Vector.ofFn fun i => m - a[i]

-- </vc-definitions>

-- <vc-theorems>
theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] :=
by
  dsimp [invert, mask]
  have hlen : (Vector.ofFn fun i => (Nat.pow 2 bitWidth - 1) - a[i]).toList.length = n := by
    simp [Vector.ofFn]
  have hidx : ∀ i : Fin n, (Vector.ofFn fun i => (Nat.pow 2 bitWidth - 1) - a[i])[i] = (Nat.pow 2 bitWidth - 1) - a[i] := by
    intro i; simp [Vector.ofFn]
  exact ⟨hlen, fun i => hidx i⟩

-- </vc-theorems>
