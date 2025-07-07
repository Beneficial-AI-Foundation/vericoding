namespace NpReshape

def reshape {n : Nat} (arr : Vector Int n) (shape : Vector Int 2) : Matrix Int (if shape[0]! > 0 then shape[0]! else n / shape[1]!) (if shape[1]! > 0 then shape[1]! else n / shape[0]!) := sorry

theorem reshape_spec {n : Nat} (arr : Vector Int n) (shape : Vector Int 2)
  (h1 : ∀ i : Fin 2, shape[i] > 0 ∨ shape[i] = -1)
  (h2 : ¬(shape[0]! = -1 ∧ shape[1]! = -1))
  (h3 : if shape[0]! > 0 ∧ shape[1]! > 0 then shape[0]! * shape[1]! = n
        else if shape[0]! = -1 then n % shape[1]! = 0
        else n % shape[0]! = 0) :
  let ret := reshape arr shape
  (if shape[0]! > 0 then ret.toList.length / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = shape[0]!
   else ret.toList.length / (if shape[1]! > 0 then shape[1]! else n / shape[0]!) = n / shape[1]!) ∧
  (∀ i : Nat, i < n → ret[i / ret.toList.length]![i % ret.toList.length]! = arr[i]!) := sorry

end NpReshape
