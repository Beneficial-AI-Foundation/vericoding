import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
def shiftLeftIntHelper (x : Int) (shift : Nat) : Int := x * (2 ^ shift : Int)
-- </vc-helpers>

-- <vc-definitions>
def shiftLeftInt (x : Int) (shift : Nat) : Int :=
x * (2 ^ shift : Int)

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n :=
Vector.ofFn fun i => shiftLeftInt a[i] b[i]
-- </vc-definitions>

-- <vc-theorems>
theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) :=
by
  constructor
  · -- First part: prove length is n
    simp only [leftShift]
    rw [Vector.toList_ofFn]
    simp only [List.length_ofFn]
  · -- Second part: prove element-wise equality
    intro i
    simp only [leftShift]
    -- Direct simplification without explicit rewrite
    simp [Vector.getElem_ofFn]
-- </vc-theorems>
