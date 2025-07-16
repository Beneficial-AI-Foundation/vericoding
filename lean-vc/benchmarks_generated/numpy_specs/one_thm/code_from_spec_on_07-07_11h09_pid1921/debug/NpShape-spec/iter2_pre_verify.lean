namespace NpShape

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Array (Array α)

inductive arrays where
  | arrayOne : Vector Float n → arrays
  | arrayTwo : Matrix Float m n → arrays
  | arrayThree : Array (Array (Array Float)) → arrays

def shape'' (a : arrays) : Vector Int (match a with | .arrayOne _ => 1 | .arrayTwo _ _ => 2 | .arrayThree _ => 3) := 
  match a with
  | .arrayOne arr => ⟨[arr.toList.length], by simp⟩
  | .arrayTwo arr => ⟨[arr.size, if arr.size > 0 then arr[0]!.size else 0], by simp⟩
  | .arrayThree arr => ⟨[arr.size, if arr.size > 0 then arr[0]!.size else 0, if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0], by simp⟩

def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := 
  ⟨[m, n], by simp⟩

theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne arr => ret.toList.length = 1 ∧ ret[0]! = arr.toList.length
  | .arrayTwo arr => ret.toList.length = 2 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0)
  | .arrayThree arr => ret.toList.length = 3 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0) ∧ ret[2]! = (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) := by
  simp [shape'']
  cases a with
  | arrayOne arr => simp [Vector.toList, Vector.get]
  | arrayTwo arr => simp [Vector.toList, Vector.get]
  | arrayThree arr => simp [Vector.toList, Vector.get]

theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  (ret.toList.length = 2) ∧
  (ret[0]! = m ∧ ret[1]! = n) := by
  simp [shape, Vector.toList, Vector.get]

end NpShape