namespace NpLeftShift

def shiftLeftInt (x : Int) (shift : Nat) : Int := x <<< shift

def leftShift {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftLeftInt (a[i]) (b[i]))

/- LLM HELPER -/
lemma Vector.ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/- LLM HELPER -/
lemma Vector.ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]

theorem leftShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n)
    (h : ∀ i : Fin n, b[i] < 64) :
  (leftShift a b h).toList.length = n ∧
  ∀ i : Fin n, (leftShift a b h)[i] = shiftLeftInt (a[i]) (b[i]) := by
  constructor
  · simp [leftShift, Vector.ofFn_length]
  · intro i
    simp [leftShift, Vector.ofFn_get]

end NpLeftShift