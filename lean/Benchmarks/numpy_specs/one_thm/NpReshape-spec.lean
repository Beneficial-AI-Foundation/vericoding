import Benchmarks.MatrixDef

namespace NpReshape

def reshape {n m k : Nat} (arr : Vector Int n) (shape : Vector Int 2) : Matrix m k Int := sorry

theorem reshape_spec {n m k : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]'sorry = -1 ∧ shape[1]'sorry = -1))
  (h3 : m * k = n) :
  let ret := @reshape n m k arr shape
  (ret.toList.length = m * k) ∧
  (∀ i : Nat, i < n → (ret[i / k]'sorry)[i % k]'sorry = arr[i]'sorry) := sorry

end NpReshape
