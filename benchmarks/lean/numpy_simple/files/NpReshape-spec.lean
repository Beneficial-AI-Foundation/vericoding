-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reshape {n : Nat} (arr : Vector Int n) (shape : Vector Nat 2) : Matrix (if shape[0]! > 0 then shape[0]! else n / shape[1]!) (if shape[1]! > 0 then shape[1]! else n / shape[0]!) Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reshape_spec {n : Nat} (arr : Vector Int n) (shape : Vector Nat 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = 0)
  (h2 : ¬(shape[0]! = 0 ∧ shape[1]! = 0))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = 0 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  (if shape[0]! > 0 then ret.size / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = shape[0]!
   else ret.size / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = n / shape[1]!) ∧
  (∀ i : Nat, i < n → ret[(i / ret.size, i % ret.size)]! = arr[i]!) :=
sorry
-- </vc-theorems>