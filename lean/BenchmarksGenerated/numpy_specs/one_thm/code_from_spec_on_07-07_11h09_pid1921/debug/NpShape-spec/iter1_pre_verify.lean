namespace NpShape

inductive arrays where
  | arrayOne : Vector Float n → arrays
  | arrayTwo : Matrix Float m n → arrays
  | arrayThree : Array (Array (Array Float)) → arrays

def shape'' (a : arrays) : Vector Int (match a with | .arrayOne _ => 1 | .arrayTwo _ _ => 2 | .arrayThree _ => 3) := 
  match a with
  | .arrayOne arr => Vector.cons arr.toList.length Vector.nil
  | .arrayTwo arr => Vector.cons arr.toList.length (Vector.cons (if arr.toList.length > 0 then arr[0]!.toList.length else 0) Vector.nil)
  | .arrayThree arr => Vector.cons arr.size (Vector.cons (if arr.size > 0 then arr[0]!.size else 0) (Vector.cons (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) Vector.nil))

def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := 
  Vector.cons m (Vector.cons n Vector.nil)

theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne arr => ret.toList.length = 1 ∧ ret[0]! = arr.toList.length
  | .arrayTwo arr => ret.toList.length = 2 ∧ ret[0]! = arr.toList.length ∧ ret[1]! = (if arr.toList.length > 0 then arr[0]!.toList.length else 0)
  | .arrayThree arr => ret.toList.length = 3 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0) ∧ ret[2]! = (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) := by
  simp [shape'']
  cases a with
  | arrayOne arr => simp [Vector.toList_cons, Vector.get_cons_zero]
  | arrayTwo arr => simp [Vector.toList_cons, Vector.get_cons_zero, Vector.get_cons_succ]
  | arrayThree arr => simp [Vector.toList_cons, Vector.get_cons_zero, Vector.get_cons_succ]

theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  (ret.toList.length = 2) ∧
  (ret[0]! = m ∧ ret[1]! = n) := by
  simp [shape, Vector.toList_cons, Vector.get_cons_zero, Vector.get_cons_succ]

end NpShape