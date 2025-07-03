namespace NpLeftShift

/- LLM HELPER -/
def shiftLeftInt (x : Int) (shift : Nat) : Int := x * (2 : Int) ^ shift

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftLeftInt (a[i]) (b[i]))

theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) := by
  constructor
  · simp [leftShift, Vector.ofFn]
  · intro i
    simp [leftShift, Vector.ofFn]

end NpLeftShift