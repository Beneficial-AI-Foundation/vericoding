namespace NpShape

inductive arrays where
  | arrayOne : Vector Float n → arrays
  | arrayTwo : Matrix Float m n → arrays
  | arrayThree : Array (Array (Array Float)) → arrays

def shape'' (a : arrays) : Vector Int (match a with | .arrayOne _ => 1 | .arrayTwo _ _ => 2 | .arrayThree _ => 3) := sorry

def shape {m n : Nat} (a : Matrix Float m n) : Vector Int 2 := sorry

theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne arr => ret.toList.length = 1 ∧ ret[0]! = arr.toList.length
  | .arrayTwo arr => ret.toList.length = 2 ∧ ret[0]! = arr.toList.length ∧ ret[1]! = (if arr.toList.length > 0 then arr[0]!.toList.length else 0)
  | .arrayThree arr => ret.toList.length = 3 ∧ ret[0]! = arr.size ∧ ret[1]! = (if arr.size > 0 then arr[0]!.size else 0) ∧ ret[2]! = (if arr.size > 0 ∧ arr[0]!.size > 0 then arr[0]![0]!.size else 0) := sorry

theorem shape_spec {m n : Nat} (a : Matrix Float m n) :
  let ret := shape a
  (ret.toList.length = 2) ∧
  (ret[0]! = m ∧ ret[1]! = n) := sorry

end NpShape
