namespace NpShape

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Array (Array α)

inductive arrays where
  | arrayOne : ∀ n : Nat, Vector Float n → arrays
  | arrayTwo : ∀ m n : Nat, Matrix Float m n → arrays
  | arrayThree : Array (Array (Array Float)) → arrays

-- LLM HELPER
def get_array_dimension (a : arrays) : Nat :=
  match a with
  | .arrayOne _ _ => 1
  | .arrayTwo _ _ _ => 2
  | .arrayThree _ => 3

def shape'' (a : arrays) : Vector Int (get_array_dimension a) := 
  match a with
  | .arrayOne n arr => Vector.mk #[arr.size]
  | .arrayTwo m n arr => Vector.mk #[arr.size, if arr.size > 0 then arr[0]!.size else 0]
  | .arrayThree arr => Vector.mk #[arr.size, if arr.size > 0 then arr[0]!.size else 0, if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0]

def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := 
  Vector.mk #[m, n]

theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne n arr => ret.size = 1 ∧ ret[0]! = arr.size
  | .arrayTwo m n arr => ret.size = 2 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0)
  | .arrayThree arr => ret.size = 3 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0) ∧ ret[2]! = (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) := by
  simp [shape'', get_array_dimension]
  cases a with
  | arrayOne n arr => simp [Vector.mk, Vector.size, Vector.get]
  | arrayTwo m n arr => simp [Vector.mk, Vector.size, Vector.get]
  | arrayThree arr => simp [Vector.mk, Vector.size, Vector.get]

theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  (ret.size = 2) ∧
  (ret[0]! = m ∧ ret[1]! = n) := by
  simp [shape, Vector.mk, Vector.size, Vector.get]

end NpShape