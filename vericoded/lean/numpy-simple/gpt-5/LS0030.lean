import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_get_ofFn {α} {n} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simpa using Vector.get_ofFn f i
-- </vc-helpers>

-- <vc-definitions>
def shiftLeftInt (x : Int) (shift : Nat) : Int :=
x * (2 ^ shift)

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n :=
Vector.ofFn (fun i => shiftLeftInt (a[i]) (b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) :=
by
  constructor
  · simpa [leftShift]
  · intro i
    simp [leftShift, shiftLeftInt]
-- </vc-theorems>
