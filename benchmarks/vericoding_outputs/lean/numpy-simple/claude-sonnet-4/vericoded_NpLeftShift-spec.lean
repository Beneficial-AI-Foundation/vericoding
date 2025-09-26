import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for vector operations
lemma Vector.toList_ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) :
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.toList_ofFn]

lemma Vector.get_ofFn_eq {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.get_ofFn]
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
⟨by simp [leftShift], fun i => by simp [leftShift]⟩
-- </vc-theorems>
