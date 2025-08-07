import benchmarks.MatrixDef

namespace NpShape

inductive arrays where
  | arrayOne : Vector Float n → arrays
  | arrayTwo : Matrix m n Float → arrays
  | arrayThree : Array (Array (Array Float)) → arrays

def shape'' (a : arrays) : Vector Int (match a with | .arrayOne _ => 1 | .arrayTwo _ => 2 | .arrayThree _ => 3) := sorry

def shape {m n : Nat} (a : Matrix m n Float) : Vector Int 2 := sorry

theorem shape''_spec (a : arrays) :
  let ret := shape'' a
  match a with
  | .arrayOne arr => ret.toList.length = 1 ∧ ret[0]'sorry = arr.toList.length
  | .arrayTwo arr => ret.toList.length = 2 ∧ ret[0]'sorry = arr.toList.length ∧ ret[1]'sorry = 0
  | .arrayThree arr => ret.toList.length = 3 ∧ ret[0]'sorry = arr.size ∧ ret[1]'sorry = 0 ∧ ret[2]'sorry = 0 := sorry

theorem shape_spec {m n : Nat} (a : Matrix m n Float) :
  let ret := shape a
  (ret.toList.length = 2) ∧
  (ret[0]'sorry = m ∧ ret[1]'sorry = n) := sorry

end NpShape
