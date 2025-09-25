-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Nat 2) : Matrix (shape[0]!) (shape[1]!) Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Nat 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  (ret.size = shape[0]! * shape[1]!) ∧
  (∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[(i,j)]! = a[i]! else ret[(i,j)]! = a[j]!) :=
sorry
-- </vc-theorems>