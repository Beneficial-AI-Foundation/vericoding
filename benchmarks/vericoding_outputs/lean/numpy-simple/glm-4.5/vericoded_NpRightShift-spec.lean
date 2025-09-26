import Mathlib
-- <vc-preamble>
def shiftRightInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs >>> n)
  else
    -(Int.ofNat (((-x).natAbs - 1) >>> n + 1))
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper for vector length equality
def Vector.ofFn_length {α : Type} {n : Nat} (f : Fin n → α) :
    (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, List.length_ofFn]

-- LLM HELPER: Helper for vector element access
def Vector.ofFn_getElem {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.getElem_ofFn]
-- </vc-helpers>

-- <vc-definitions>
def rightShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  (h : ∀ i : Fin n, b[i] < 64) : Vector Int n :=
Vector.ofFn fun i => shiftRightInt (a[i]) (b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem rightShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
  (h : ∀ i : Fin n, b[i] < 64) :
  (rightShift a b h).toList.length = n ∧
  ∀ i : Fin n, (rightShift a b h)[i] = shiftRightInt (a[i]) (b[i]) :=
by
  unfold rightShift
  constructor
  -- Prove the length is correct
  apply Vector.ofFn_length
  -- Prove each element is correct
  intro i
  apply Vector.ofFn_getElem
-- </vc-theorems>
