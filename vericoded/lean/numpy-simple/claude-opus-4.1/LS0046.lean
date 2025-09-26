import Mathlib
-- <vc-preamble>
def shiftRightInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs >>> n)
  else
    -(Int.ofNat (((-x).natAbs - 1) >>> n + 1))
-- </vc-preamble>

-- <vc-helpers>
-- No helper code needed for this implementation
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
  constructor
  · simp [rightShift]
  · intro i
    simp [rightShift]
-- </vc-theorems>
