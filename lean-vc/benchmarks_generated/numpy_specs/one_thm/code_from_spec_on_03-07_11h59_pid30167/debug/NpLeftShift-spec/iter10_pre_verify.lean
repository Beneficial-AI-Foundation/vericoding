namespace NpLeftShift

def shiftLeftInt (x : Int) (shift : Nat) : Int := x * (2 ^ shift)

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftLeftInt (a[i]) (b[i]))

theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) := by
  constructor
  · simp [leftShift, Vector.toList_ofFn]
  · intro i
    simp [leftShift, Vector.ofFn_get]

end NpLeftShift