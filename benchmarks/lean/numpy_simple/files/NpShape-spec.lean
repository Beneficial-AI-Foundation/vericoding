-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n

inductive arrays where
  | arrayOne : Array Float → arrays
  | arrayTwo : Array (Array Float) → arrays
  | arrayThree : Array (Array (Array Float)) → arrays
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shape'' (a : arrays) : Vector Nat (match a with | .arrayOne _ => 1 | .arrayTwo _ => 2 | .arrayThree _ => 3) :=
sorry

def shape {m n : Nat} (a : Matrix m n Float) : Vector Nat 2 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne arr => ret.toList.length = 1 ∧ ret[0]! = arr.toList.length
  | .arrayTwo arr => ret.toList.length = 2 ∧ ret[0]! = arr.toList.length ∧ ret[1]! = (if arr.toList.length > 0 then arr[0]!.toList.length else 0)
  | .arrayThree arr => ret.toList.length = 3 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0) ∧ ret[2]! = (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) :=
sorry

theorem shape_spec {m n : Nat} (a : Matrix m n Float) :
  let ret := shape a
  (ret.toList.length = 2) ∧
  (ret[0]! = m ∧ ret[1]! = n) :=
sorry
-- </vc-theorems>